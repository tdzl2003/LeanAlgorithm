import Lean
import Algorithm.TimeCost.Def

open Lean Meta Elab Term Command

open Expr

partial def exprToWithCost(expr prevCost: Expr): MetaM Expr := do
  let type ← inferType expr
  logInfo m!"Working: {expr} with type {type}"

  match expr with
  | fvar _ =>
      let ret :=  Expr.app
          (Expr.app (Expr.app (Expr.const `Algorithm.WithCost.mk []) type) prevCost)
          expr
      logInfo m!"Ret: {ret}"
      return ret
  | lam name type body bi =>
      logInfo m!"lam {name} {type} {body}"
      return (Expr.lam name type
          (← withLocalDecl name bi type
            (fun fvar => do
              let body := body.instantiate1 fvar
              let ret ← exprToWithCost body prevCost
              let ret := ret.liftLooseBVars 0 1
              let ret := ret.replaceFVar fvar $ Expr.bvar 0
              return ret
            )
          )
        bi)
  -- | app a b =>
  --     logInfo m!"app {a} {b}"
  --     match a with
  --     | _ => throwError m!"TODO"
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
              let newDef := ← exprToWithCost val.value (Expr.lit (.natVal 0))
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

def test(a b: Nat) := a

#eval Algorithm.WithCost.mk 2 2

#autogen_fun_with_cost test

#print test.withCost

#eval test.withCost 1 2
