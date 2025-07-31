import Mathlib
import Algorithm

open Asymptotics Algorithm

-- 斐波那契函数的定义
def fac: ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1) * fac n

-- 期待通过Meta Programming自动生成这个函数：
#autogen_fun_with_cost fac

#check Nat.brecOn
#check fac.match_1
#check Nat.below
