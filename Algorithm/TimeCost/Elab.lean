import Lean
import Algorithm.TimeCost.Def

open Lean Meta Elab Term Command

open Expr

def ZeroExpr := Expr.lit (.natVal 0)

def Nat.succ.withCost := Nat.succ

def Nat.add.withCost := Nat.add

namespace Algorithm

def isWithCostType(t: Expr): Bool :=
  t.isApp ∧ t.appFn!.isConst ∧ t.appFn!.constName! = `Algorithm.WithCost

def getValueType(t: Expr): Expr :=
  if isWithCostType t then
    t.getArg! 0
  else
    t

/--
  expr: 当前的表达式分支
  prevCost: 表示之前let语句中所含所有开销的变量
-/
partial def exprToWithCost(expr: Expr)(prevCost: Option Expr): MetaM Expr := do
  let type ← inferType expr
  logInfo m!"Working: {expr} with type {type}"

  let withPrevCost(expr: Expr): MetaM Expr := do
    match prevCost with
    | none => return expr
    | some prevCost => do
        let type ← inferType expr
        return Expr.app
          (Expr.app (Expr.app (Expr.const `Algorithm.WithCost.mk []) type) prevCost) expr

  let addPrevCost(expr: Expr): MetaM Expr := do
    match prevCost with
    | none => return expr
    | some prevCost => do
        let type ← inferType expr
        let valueType := getValueType type
        return Expr.app
          (Expr.app (Expr.app (Expr.const `Algorithm.WithCost.addCost []) valueType) expr) prevCost

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
        return ← addPrevCost newExpr
      logInfo m!"Ret"
      withPrevCost expr
  | lam name type body bi =>
      logInfo m!"lam {name} {type} {body}"
      let newExpr := (Expr.lam name type
          (← withLocalDecl name bi type
            (fun fvar => do
              let body := body.instantiate1 fvar
              let ret ← exprToWithCost body none
              let ret := ret.liftLooseBVars 0 1
              let ret := ret.replaceFVar fvar $ Expr.bvar 0
              return ret
            )
          )
        bi)
      withPrevCost newExpr
  | app f a =>
      let newF ← exprToWithCost f none
      let newA ← exprToWithCost a none
      let newFType ← inferType newF
      let newAType ← inferType newA
      let fValType := getValueType newFType
      let retType := fValType.bindingBody!
      let retValType := getValueType retType

      logInfo m!"retValType {retValType}"

      -- 最内层的调用
      let genApply(f: Expr)(a: Expr): Expr :=
        let app := Expr.app f a

        if isWithCostType retType then
          -- 带类型调用，增加消耗 ret.addCost 1
          let retValueType := getValueType retType
          let addCost := Expr.const `Algorithm.WithCost.addCost []
          let addCost := Expr.app addCost retValueType
          let addCost := Expr.app addCost app
          Expr.app addCost (Expr.lit (.natVal 1))
        else
          -- 不带类型调用，构造消耗 {cost:= 1, val:= ret}
          let mkCost := Expr.const `Algorithm.WithCost.mk []
          let mkCost := Expr.app mkCost retType
          let mkCost := Expr.app mkCost (Expr.lit (.natVal 1))
          Expr.app mkCost app

      -- 包装Arg
      let genApply1(f: Expr): Expr :=
        if isWithCostType newAType then
          -- a.andThen λa =>...
          let AValueType := getValueType newAType
          -- f a
          let expr := genApply f (Expr.bvar 0)
          -- λa => f a
          let f := Expr.lam `a AValueType expr .default
          -- a.andThen
          let expr := Expr.const `Algorithm.WithCost.andThen []
          let expr := Expr.app expr AValueType
          let andThen := Expr.app expr retValType

          let expr := Expr.app andThen newA
          Expr.app expr f
        else
          -- 直接调用
          genApply f newA

      if isWithCostType newFType then
        -- f.andThen λf => ...
        -- f a
        let expr := genApply1 (Expr.bvar 0)
        -- λa => f a
        let f := Expr.lam `a fValType expr .default
        -- a.andThen
        let expr := Expr.const `Algorithm.WithCost.andThen []
        let expr := Expr.app expr fValType
        let andThen := Expr.app expr retValType

        let expr := Expr.app andThen newF
        return Expr.app expr f
      else
        -- 直接调用
        return genApply1 newF

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
              let newDef := ← exprToWithCost val.value none
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

def test(a b: Nat) := Nat.add a b

#autogen_fun_with_cost Algorithm.test

#print test.withCost

#eval test.withCost 2 4

end Algorithm
