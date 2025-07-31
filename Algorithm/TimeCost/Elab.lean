import Lean
import Algorithm.TimeCost.Def

open Lean Meta Elab Term Command

open Expr

namespace Algorithm

def isWithCostType(t: Expr): Bool :=
  t.isApp ∧ t.appFn!.isConst ∧ t.appFn!.constName! = `Algorithm.WithCost

def getValueType(t: Expr): Expr :=
  if isWithCostType t then
    t.getArg! 0
  else
    t

partial def isPropOrTypeFuncType(t: Expr): Bool :=
  t.isSort ∨ t.isForall ∧ isPropOrTypeFuncType t.bindingBody!

-- 处理出现的所有类型，为所有函数的最终返回值增加WithCost
def withCostForLastReturnType(type: Expr): Expr :=
  match type with
  | forallE binderName binderType body binderInfo =>
        let binderType := if binderType.isForall then withCostForLastReturnType binderType else binderType
        let body := withCostForLastReturnType body
        .forallE binderName binderType body binderInfo
  | _ =>
    if isPropOrTypeFuncType type then
      type
    else
      Expr.app (Expr.const `Algorithm.WithCost []) type

/--
  expr: 当前的表达式分支
  prevCost: 表示之前let语句中所含所有开销的变量
-/
partial def exprToWithCost(expr: Expr)(prevCost: Option Expr): MetaM Expr := do
  let type ← inferType expr
  logInfo m!"Working: {expr} with type {type}"

  let typetype ← inferType type
  if typetype.isProp then
    return expr

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
  | fvar fvarId =>
      logInfo m!"fvar {fvarId.name}"
      -- 返回具体的值并叠加prevCost
      withPrevCost expr
  | lit _ =>
      logInfo m!"lit {expr}"
      withPrevCost expr
  | const name us =>
      -- 是一个函数
      logInfo m!"const {expr} {type} {type.isForall}"

      if type.isForall then
        let newExpr := Expr.const (Name.str name "withCost") us
        let newExprType ← inferType newExpr
        if newExprType.isForall then
          -- 多元函数？可以直接调用，包装当前cost并返回
          return ← withPrevCost newExpr

        -- 已经包装好的函数，附加当前cost
        return ← addPrevCost newExpr
      withPrevCost expr
  | lam name type body bi =>
      let typetype ← inferType type
      logInfo m!"lam name={name} type={type} body={body} typetype={typetype} typetype.sortLevel={typetype.sortLevel!}"
      let type := if type.isForall ∧ typetype.sortLevel! == 1 then withCostForLastReturnType type else type
      logInfo m!"{type}"
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
  | proj typeName idx struct =>
      logInfo m!"proj {typeName} {idx} {struct}"
      let newStruct ← exprToWithCost struct none
      let newStructType ← inferType newStruct
      logInfo m!"newStruct={newStruct} newStructType={newStructType}"
      if isWithCostType newStructType then
        throwError m!"TODO"
      else
        return expr
  | app f a =>
      logInfo m!"app {f} {a}"
      let typetype ← inferType type
      if type.isType ∨ type.isProp ∨ typetype.sortLevel! != 1 then
        return expr
      let newF ← exprToWithCost f none
      let newA ← exprToWithCost a none
      logInfo m!"mapping f: {f} ==> {newF}"
      logInfo m!"mapping a: {a} ==> {newA}"
      let newFType ← inferType newF
      let newAType ← inferType newA
      let fValType := getValueType newFType

      -- 最内层的调用
      let genApply(f: Expr)(a: Expr): MetaM Expr := do
        let app := Expr.app f a
        let retType ← inferType app
        if isPropOrTypeFuncType newAType ∨ isPropOrTypeFuncType retType then
          return app
        else
          if isWithCostType retType then
            -- 返回值带Cost，增加消耗 ret.addCost 1
            let retValueType := getValueType retType
            let addCost := Expr.const `Algorithm.WithCost.addCost []
            let addCost := Expr.app addCost retValueType
            let addCost := Expr.app addCost app
            return Expr.app addCost (Expr.lit (.natVal 1))
          else
            -- 返回值不带Cost，构造消耗 {cost:= 1, val:= ret}
            let mkCost := Expr.const `Algorithm.WithCost.mk []
            let mkCost := Expr.app mkCost retType
            let mkCost := Expr.app mkCost (Expr.lit (.natVal 1))
            return Expr.app mkCost app

      -- 包装Arg
      let genApply1(f: Expr)(a: Expr): MetaM Expr := do

        if isWithCostType newAType then
          -- a.andThen λa =>...
          let newAType ← inferType a
          let AValueType := getValueType newAType
          -- ...
          let expr ← withLocalDecl `a BinderInfo.default AValueType fun avar => do
            let ret ← genApply f avar
            let ret := ret.liftLooseBVars 0 1
            let ret := ret.replaceFVar avar $ Expr.bvar 0
            return ret

          -- λa => f a
          let f := Expr.lam `a AValueType expr .default
          let fType ← inferType f
          let retValType := getValueType fType.bindingBody!
          -- a.andThen
          let expr := Expr.const `Algorithm.WithCost.andThen []
          let expr := Expr.app expr AValueType
          let andThen := Expr.app expr retValType

          let expr := Expr.app andThen a
          return Expr.app expr f
        else
          -- 直接调用
          return ← genApply f a

      if isWithCostType newFType then
        -- f.andThen λf => ...

        let expr ← withLocalDecl `f BinderInfo.default fValType fun fvar => do
          let ret ← genApply1 fvar newA
          let ret := ret.liftLooseBVars 0 1
          let ret := ret.replaceFVar fvar $ Expr.bvar 0
          return ret


        -- λa => f a
        let f := Expr.lam `a fValType expr .default
        let fType ← inferType f
        let retValType := getValueType fType.bindingBody!
        -- a.andThen
        let expr := Expr.const `Algorithm.WithCost.andThen []
        let expr := Expr.app expr fValType
        let andThen := Expr.app expr retValType

        let expr := Expr.app andThen newF
        return Expr.app expr f
      else
        -- 直接调用
        return ← genApply1 newF newA

  | forallE binderName binderType body binderInfo =>
      let binderType := if binderType.isForall then withCostForLastReturnType binderType else binderType
      let body := withCostForLastReturnType body
      return .forallE binderName binderType body binderInfo
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

end Algorithm
