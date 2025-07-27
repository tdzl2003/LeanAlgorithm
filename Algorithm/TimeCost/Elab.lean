import Lean

open Lean Meta Elab Term

syntax (name := time_cost_term)(priority := 0) "time_cost" term : term

partial def time_cost_for_syntax: Syntax → TermElabM Expr := fun stx =>
  withIncRecDepth do
    match stx with
    | `($_:num) => return mkNatLit 1
    | `($_:ident) => return mkNatLit 1
    | `($a + $b) =>
        let acost ← time_cost_for_syntax a
        let bcost ← time_cost_for_syntax b
        return ← mkAdd (mkNatLit 1) (← mkAdd acost bcost)
    | `(($stx)) => time_cost_for_syntax stx
    | _ => throwError "Syntax {stx} not supported for time_complex"

@[term_elab time_cost_term]
def time_cost_term_impl : TermElab := fun stx type? => do
  match stx with
  | `(time_cost $stx1) => return ← time_cost_for_syntax stx1
  | _ => throwError "Bad syntax"
