-- ============================================
-- Project Euler: Problem Zero
-- 最初の N 個の平方数のうち、奇数の平方数の合計を求める
-- ============================================

namespace ProjectEuler

-- ============================================
-- 実装
-- ============================================

/-- 1² から n² までの奇数平方数の合計（再帰的定義） -/
def sumOddSquares : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 == 1
    then sumOddSquares n + (n + 1) * (n + 1)
    else sumOddSquares n

/-- 閉じた公式: m(2m-1)(2m+1)/3 （m = 1からnまでの奇数の個数） -/
def sumOddSquaresFormula (n : Nat) : Nat :=
  let m := (n + 1) / 2
  m * (2 * m - 1) * (2 * m + 1) / 3

-- 計算結果の確認
#eval sumOddSquares 5               -- 35 (= 1² + 3² + 5²)
#eval sumOddSquaresFormula 5         -- 35
#eval sumOddSquaresFormula 510000    -- 22108499999915000

-- ============================================
-- 証明: 基本性質
-- ============================================

-- 空の場合は 0
theorem sumOddSquares_zero : sumOddSquares 0 = 0 := rfl

-- 具体値の検証（decide = カーネルで計算して検証）
theorem sumOddSquares_eq_1 : sumOddSquares 1 = 1 := by decide
theorem sumOddSquares_eq_2 : sumOddSquares 2 = 1 := by decide
theorem sumOddSquares_eq_3 : sumOddSquares 3 = 10 := by decide
theorem sumOddSquares_eq_5 : sumOddSquares 5 = 35 := by decide

-- ============================================
-- 証明: n² の偶奇は n の偶奇と一致する
-- ============================================

theorem sq_mod2_eq (n : Nat) : n * n % 2 = n % 2 := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  cases h with
  | inl h => simp [Nat.mul_mod, h]
  | inr h => simp [Nat.mul_mod, h]

-- ============================================
-- 証明: 再帰版と公式版の一致
-- ============================================

-- 小さい値は decide（カーネル計算）で検証
theorem formula_eq_sum_5 :
    sumOddSquaresFormula 5 = sumOddSquares 5 := by decide

theorem formula_eq_sum_10 :
    sumOddSquaresFormula 10 = sumOddSquares 10 := by decide

-- 大きい値は native_decide（ネイティブコンパイルして検証）
theorem formula_eq_sum_100 :
    sumOddSquaresFormula 100 = sumOddSquares 100 := by native_decide

theorem formula_eq_sum_1000 :
    sumOddSquaresFormula 1000 = sumOddSquares 1000 := by native_decide

-- ============================================
-- 証明: 問題の答え
-- ============================================

/-- 最初の510000個の平方数のうち、奇数平方数の合計は22108499999915000 -/
theorem euler_problem_zero :
    sumOddSquaresFormula 510000 = 22108499999915000 := by native_decide

end ProjectEuler
