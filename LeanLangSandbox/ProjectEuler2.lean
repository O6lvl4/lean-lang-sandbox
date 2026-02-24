-- ============================================
-- Project Euler: Problem 2
-- 400万以下の偶数フィボナッチ数の合計を求める
-- ============================================

namespace ProjectEuler2

-- ============================================
-- 実装
-- ============================================

/-- フィボナッチ数（0始まり: 0, 1, 1, 2, 3, 5, 8, ...） -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- limit 以下の偶数フィボナッチ数の合計
    fuel でステップ数を制限して停止性を保証 -/
def sumEvenFib (limit : Nat) : Nat :=
  go limit 1 1 0
where
  go : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
    if a > limit then acc
    else
      let newAcc := if a % 2 == 0 then acc + a else acc
      go fuel b (a + b) newAcc

-- 計算結果の確認
#eval sumEvenFib 10         -- 10 (= 2 + 8)
#eval sumEvenFib 100        -- 44 (= 2 + 8 + 34)
#eval sumEvenFib 4000000    -- 4613732

-- ============================================
-- 証明: フィボナッチ数の基本性質
-- ============================================

theorem fib_0 : fib 0 = 0 := rfl
theorem fib_1 : fib 1 = 1 := rfl
theorem fib_2 : fib 2 = 1 := rfl
theorem fib_3 : fib 3 = 2 := rfl
theorem fib_4 : fib 4 = 3 := rfl
theorem fib_5 : fib 5 = 5 := rfl
theorem fib_6 : fib 6 = 8 := rfl
theorem fib_10 : fib 10 = 55 := by decide
theorem fib_20 : fib 20 = 6765 := by native_decide

-- フィボナッチ数の漸化式
theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

-- ============================================
-- 証明: 3つごとのフィボナッチ数が偶数
-- fib(0)=0, fib(3)=2, fib(6)=8, fib(9)=34, ...
-- ============================================

theorem fib_0_even : fib 0 % 2 = 0 := by decide
theorem fib_3_even : fib 3 % 2 = 0 := by decide
theorem fib_6_even : fib 6 % 2 = 0 := by decide
theorem fib_9_even : fib 9 % 2 = 0 := by decide
theorem fib_12_even : fib 12 % 2 = 0 := by decide

-- 3つごと以外は奇数
theorem fib_1_odd : fib 1 % 2 = 1 := by decide
theorem fib_2_odd : fib 2 % 2 = 1 := by decide
theorem fib_4_odd : fib 4 % 2 = 1 := by decide
theorem fib_5_odd : fib 5 % 2 = 1 := by decide

-- ============================================
-- 証明: 具体値の検証
-- ============================================

theorem sumEvenFib_10 : sumEvenFib 10 = 10 := by native_decide
theorem sumEvenFib_100 : sumEvenFib 100 = 44 := by native_decide

-- ============================================
-- 証明: 問題の答え
-- ============================================

/-- 400万以下の偶数フィボナッチ数の合計は4613732 -/
theorem euler_problem_2 :
    sumEvenFib 4000000 = 4613732 := by native_decide

end ProjectEuler2
