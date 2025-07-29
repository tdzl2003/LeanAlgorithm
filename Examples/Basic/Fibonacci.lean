import Mathlib
import Algorithm

open Asymptotics

-- 斐波那契函数的定义
def fib: ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

-- 期待通过Meta Programming自动生成这个函数：
def fib.withCost : ℕ → WithCost ℕ
  | 0 => ⟨1, 0⟩
  | 1 => ⟨1, 1⟩
  | n+2 => fib.withCost (n+1) + fib.withCost n


-- 正确性证明：
-- f_0 = 0, f_1 = 1, f_n = f_{n-1}+f_{n-2} for n ≥ 2
theorem fib_is_correct:
  fib 0 = 0 ∧ fib 1 = 1 ∧ ∀ x ≥ 2, fib x = fib (x-1) + fib (x-2) := by
  and_intros
  . simp only [fib]
  . simp only [fib]
  . intro x hx
    conv_lhs =>
      unfold fib
    split
    . linarith
    . linarith
    simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, Nat.reduceSubDiff,
      Nat.add_left_cancel_iff]

-- 时间复杂度证明
theorem fib_time_complexity:
  (λ n => ((fib.withCost n).cost : ℝ)) =O[Filter.atTop] (λ n => ((√5 + 1) / 2) ^ n) := by
  sorry
