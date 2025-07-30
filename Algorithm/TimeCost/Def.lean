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
    包装一个一元函数，没有额外代价（但apply的时候会产生代价）
  -/
  @[simp]
  def WithCost.wrapF1{α β: Type} (f: α → β): WithCost (α → WithCost β) :=
    WithCost.wrap λ a => WithCost.wrap (f a)

  /--
    包装一个二元函数，没有额外代价（但apply的时候会产生代价）
  -/
  @[simp]
  def WithCost.wrapF2{α1 α2 β: Type} (f: α1 → α2 → β) :=
    WithCost.wrap λ a => WithCost.wrapF1 (f a)

  /--
    包装一个三元函数，没有额外代价（但apply的时候会产生代价）
  -/
  @[simp]
  def WithCost.wrapF3{α1 α2 α3 β: Type} (f: α1 → α2 → α3 → β) :=
    WithCost.wrap λ a => WithCost.wrapF2 (f a)

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
  def WithCost.applyF{α β γ: Type} (f: WithCost (α → β → γ))(a: WithCost α): WithCost (β→γ) :=
    WithCost.mk (f.cost + a.cost) (f.val a.val)

end Algorithm
