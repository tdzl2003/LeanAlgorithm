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

  /--
    为一个结果附加额外的代价
  -/
  @[simp]
  def WithCost.addCost (a: WithCost α)(cost: Nat) : WithCost α :=
    ⟨a.cost + cost, a.val⟩

  /--
    调用一个包装函数
  -/
  @[simp]
  def WithCost.apply (f: WithCost (α → WithCost β))(a: WithCost α): WithCost β :=
    (f.val a.val).addCost (f.cost + a.cost + 1)

  @[simp]
  def WithCost.applyF{α β: Type} (f: WithCost (α → β))(a: WithCost α): WithCost (β) :=
    WithCost.mk (f.cost + a.cost + 1) (f.val a.val)

end Algorithm
