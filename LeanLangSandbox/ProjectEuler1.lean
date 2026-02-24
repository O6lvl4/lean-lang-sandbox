-- ============================================
-- Project Euler: Problem 1
-- 1000未満の3または5の倍数の合計を求める
-- ============================================

namespace ProjectEuler1

-- ============================================
-- 実装
-- ============================================

/-- n未満の自然数のうち、3または5の倍数の合計（再帰的定義） -/
def sumMultiples3or5 : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if n % 3 == 0 || n % 5 == 0
    then sumMultiples3or5 n + n
    else sumMultiples3or5 n

/-- k の倍数で n 未満のものの合計: k * m * (m+1) / 2 （m = (n-1)/k） -/
def sumMultiplesOf (k n : Nat) : Nat :=
  let m := (n - 1) / k
  k * m * (m + 1) / 2

/-- 包除原理による閉じた公式: 3の倍数 + 5の倍数 - 15の倍数 -/
def sumMultiples3or5Formula (n : Nat) : Nat :=
  sumMultiplesOf 3 n + sumMultiplesOf 5 n - sumMultiplesOf 15 n

-- 計算結果の確認
#eval sumMultiples3or5 10             -- 23 (= 3 + 5 + 6 + 9)
#eval sumMultiples3or5Formula 10      -- 23
#eval sumMultiples3or5Formula 1000    -- 233168

-- ============================================
-- 証明: 基本性質
-- ============================================

theorem sumMultiples3or5_zero : sumMultiples3or5 0 = 0 := rfl

-- 具体値の検証
theorem sum_below_10 : sumMultiples3or5 10 = 23 := by decide
theorem sum_below_20 : sumMultiples3or5 20 = 78 := by decide
theorem sum_below_100 : sumMultiples3or5 100 = 2318 := by native_decide

-- ============================================
-- 証明: 包除原理の正しさ
-- 3の倍数かつ5の倍数 ⇔ 15の倍数
-- ============================================

theorem mul3_and_mul5_iff_mul15 (n : Nat) :
    (n % 3 = 0 ∧ n % 5 = 0) ↔ n % 15 = 0 := by
  constructor
  · intro ⟨h3, h5⟩
    omega
  · intro h15
    constructor <;> omega

-- ============================================
-- 証明: 再帰版と公式版の一致
-- ============================================

theorem formula_eq_10 :
    sumMultiples3or5Formula 10 = sumMultiples3or5 10 := by decide

theorem formula_eq_100 :
    sumMultiples3or5Formula 100 = sumMultiples3or5 100 := by native_decide

theorem formula_eq_1000 :
    sumMultiples3or5Formula 1000 = sumMultiples3or5 1000 := by native_decide

-- ============================================
-- 証明: 問題の答え
-- ============================================

/-- 1000未満の3または5の倍数の合計は233168 -/
theorem euler_problem_1 :
    sumMultiples3or5Formula 1000 = 233168 := by native_decide

end ProjectEuler1
