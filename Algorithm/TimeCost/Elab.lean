import Lean
import Algorithm.TimeCost.Def

open Lean Meta Elab Term Command

open Expr

def ZeroExpr := Expr.lit (.natVal 0)

/--
  expr: 当前的表达式分支
  prevCost: 表示之前let语句中所含所有开销的变量
-/
partial def exprToWithCost(expr prevCost: Expr): MetaM Expr := do
  let type ← inferType expr
  logInfo m!"Working: {expr} with type {type}"

  let withPrevCost(expr: Expr): MetaM Expr := do
    let type ← inferType expr
    return Expr.app
       (Expr.app (Expr.app (Expr.const `Algorithm.WithCost.mk []) type) prevCost) expr

  match expr with
  | fvar _ =>
      if type.isType then
        return expr

      -- 返回具体的值并叠加prevCost
      withPrevCost expr
  | const name us =>
      -- 是一个函数
      if type.isArrow then
        let newExpr := Expr.const (Name.str name "withCost") us
        let newExprType ← inferType newExpr
        if newExprType.isArrow then
          -- 多元函数？可以直接调用，包装当前cost并返回
          return ← withPrevCost newExpr

        -- 已经包装好的函数，附加当前cost
        let valueType := newExprType.getArg! 0
        let addCost := Expr.app (Expr.const `Algorithm.WithCost.addCost []) valueType
        return Expr.app (Expr.app addCost newExpr) prevCost
      logInfo m!"Ret"
      withPrevCost expr
  | lam name type body bi =>
      logInfo m!"lam {name} {type} {body}"
      let newExpr := (Expr.lam name type
          (← withLocalDecl name bi type
            (fun fvar => do
              let body := body.instantiate1 fvar
              let ret ← exprToWithCost body ZeroExpr
              let ret := ret.liftLooseBVars 0 1
              let ret := ret.replaceFVar fvar $ Expr.bvar 0
              return ret
            )
          )
        bi)
      withPrevCost newExpr
  | app f a =>
      let newF ← exprToWithCost f ZeroExpr
      let newA ← exprToWithCost a ZeroExpr

      logInfo m!"app {f} {a}"
      let newFType ← inferType newF
      let newAType ← inferType newA

      let fRetType := (newFType.getArg! 0).bindingBody!

      -- newF 的返回值类型可能是 WithCost f 也可能是 f（多元函数），支持f的情况
      if fRetType.isArrow then
        let newRetType := fRetType
        logInfo m!"newFType: {newFType}"
        let newExpr := Expr.app (Expr.const `Algorithm.WithCost.applyF []) (newAType.getArg! 0)
        let newExpr := Expr.app newExpr newRetType
        let newExpr := Expr.app newExpr newF
        let newExpr := Expr.app newExpr newA
        let newExprType ← inferType newExpr
        let addCost := Expr.app (Expr.const `Algorithm.WithCost.addCost []) (newExprType.getArg! 0)
        return Expr.app (Expr.app addCost newExpr) prevCost
      else
        let newRetType := fRetType.getArg! 0
        logInfo m!"newFType: {newFType}"
        let newExpr := Expr.app (Expr.const `Algorithm.WithCost.apply []) (newAType.getArg! 0)
        let newExpr := Expr.app newExpr newRetType
        let newExpr := Expr.app newExpr newF
        let newExpr := Expr.app newExpr newA
        let newExprType ← inferType newExpr
        let addCost := Expr.app (Expr.const `Algorithm.WithCost.addCost []) (newExprType.getArg! 0)
        return Expr.app (Expr.app addCost newExpr) prevCost
  | _ =>
      throwError m!"不支持的表达式类型：{expr}"

elab "#autogen_fun_with_cost" declName:ident : command => do
  let decl := declName.getId
  let newName := Name.str decl "withCost"

  try
    let env ← getEnv
    let info := env.find? decl
    match info with
    | none =>
      throwError m!"失败：定义未找到"
    | some info =>
      match info with
      | ConstantInfo.defnInfo val =>
          liftTermElabM <| do
              let newDef := ← exprToWithCost val.value ZeroExpr
              let newDefType := ← inferType newDef
              logInfo m!"新定义：{newDef}"
              let decl := .defnDecl {
                name        := newName
                levelParams := val.levelParams
                type        := newDefType
                value       := newDef
                safety      := .safe
                hints       := val.hints
              }
              addDecl decl
              compileDecl decl
          logInfo m!"定义：{newName}"
      | _ => throwError m!"失败：定义不是函数定义"

  catch e =>
    throwError m!"失败：{e.toMessageData}"

open Algorithm

def Nat.succ.withCost(a: Nat) := WithCost.wrap $ Nat.succ a

def Nat.add.withCost(a b: Nat) := WithCost.wrap $ Nat.add a b

def test(a b: Nat) := Nat.add a b

#autogen_fun_with_cost test

#print test.withCost

#eval (test.withCost.apply (WithCost.wrap 4)).apply (WithCost.wrap 2)
