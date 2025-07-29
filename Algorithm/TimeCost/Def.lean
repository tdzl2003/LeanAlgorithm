import Mathlib.Data.FunLike.Basic

namespace Algorithm

  structure WithCost(α: Type) where
    cost: Nat
    val: α

  @[simp]
  def WithCost.apply {f}[FunLike f α (WithCost β)] (self: WithCost f)(arg: α): WithCost β :=
    let ⟨cost1, ret⟩:= self.val arg
    ⟨self.cost + cost1, ret⟩

end Algorithm
