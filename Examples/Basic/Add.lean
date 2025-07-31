import Mathlib
import Algorithm

open Algorithm

def test(a b: Nat) := a + (a + b)

#autogen_fun_with_cost test

#print test.withCost

#eval test.withCost 2 4

example:  ∀ a b, (test.withCost a b).cost = 8 := by
  unfold test.withCost
  simp
