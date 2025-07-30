import Mathlib.Data.FunLike.Basic

namespace Algorithm

  structure WithCost(α: Type) where
    cost: Nat
    val: α

  /--
    包装一个值，没有额外代价
  -/
  @[simp]
  def WithCost.wrap (a: α): WithCost α :=
    ⟨0, a⟩

  @[simp]
  def WithCost.andThen (a: WithCost α)(f: α → WithCost β): WithCost β :=
    let r := f a.val
    ⟨a.cost + r.cost, r.val⟩

  /--
    为一个结果附加额外的代价
  -/
  @[simp]
  def WithCost.addCost (a: WithCost α)(cost: Nat) : WithCost α :=
    ⟨a.cost + cost, a.val⟩

end Algorithm
