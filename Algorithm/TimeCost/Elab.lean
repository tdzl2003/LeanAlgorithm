import Lean

open Lean Meta Elab Term

syntax (name := time_cost_term)(priority := 0) "time_cost" term : term

mutual

  partial def time_cost_for_syntax: Syntax → TermElabM Expr := fun stx =>
    withIncRecDepth do
      match stx with
      | `($_:num) => return mkNatLit 0
      | `($_:ident) => return mkNatLit 0
      | `($a + $b) =>
          let acost ← time_cost_for_syntax a
          let bcost ← time_cost_for_syntax b
          return ← mkAdd (mkNatLit 1) (← mkAdd acost bcost)
      | `($f $args*) =>
          -- 如果函数本身是计算得出的，也需要考虑合成过程的开销
          let fcost ← time_cost_for_syntax f
          -- 函数展开的计算开销
          -- let callcostFun ← time_cost_fun_for_syntax f
          -- let argsExpr ← args.mapM (λ stx => elabTerm stx none)
          -- let callcost := mkAppN callcostFun argsExpr
          -- 参数的计算开销
          let argscost ← args.foldlM (init:=mkNatLit 0) (fun sum arg => do
            let argCost ← time_cost_for_syntax arg
            mkAdd sum argCost
          )

          -- return ← mkAdd (mkNatLit 1) (← mkAdd fcost (← mkAdd argscost callcost))
          return ← mkAdd (mkNatLit 1) (← mkAdd fcost argscost)
      | `(($stx)) => time_cost_for_syntax stx
      | _ => throwError "Syntax {stx} not supported for time_cost"

  partial def time_cost_fun_for_syntax: Syntax → TermElabM Expr := fun stx =>
    withIncRecDepth do
      match stx with
      -- | _ => return mkNatLit 0
      | _ => throwError "Syntax {stx} not supported for time_cost_fun"

end

@[term_elab time_cost_term]
def time_cost_term_impl : TermElab := fun stx type? => do
  match stx with
  | `(time_cost $stx1) => return ← time_cost_for_syntax stx1
  | _ => throwError "Bad syntax"

syntax (name := time_cost_fun_term)(priority := 0) "time_cost_fun" term : term


@[term_elab time_cost_fun_term]
def time_cost_fun_term_impl : TermElab := fun stx type? => do
  match stx with
  | `(time_cost_fun $stx1) => return ← time_cost_for_syntax stx1
  | _ => throwError "Bad syntax"
