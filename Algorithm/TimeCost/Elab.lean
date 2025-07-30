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
      if type.isArrow then
        let newExpr := Expr.const (Name.str name "withCost") us
        let newExprType ← inferType newExpr
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
  | app a b =>
      logInfo m!"app {a} {b}"

      let newA ← exprToWithCost a ZeroExpr
      let newB ← exprToWithCost b ZeroExpr

      let newBType ← inferType newB
      let newRetType := (newA.getArg! 0).getForallBody.getArg! 0
      let newExpr := Expr.app (Expr.const `Algorithm.WithCost.apply []) (newBType.getArg! 0)
      let newExpr := Expr.app newExpr newRetType
      let newExpr := Expr.app newExpr newA
      let newExpr := Expr.app newExpr newB
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

def Nat.succ.withCost := WithCost.wrapF1 Nat.succ

def Nat.add.withCost := WithCost.wrapF2 Nat.add

def test(a b: Nat) := Nat.add a b

#autogen_fun_with_cost test

#print test.withCost

#eval (test.withCost.apply (WithCost.wrap 4)).apply (WithCost.wrap 2)
