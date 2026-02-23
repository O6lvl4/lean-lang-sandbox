def fizzbuzz (n : Nat) : String :=
  if n % 15 == 0 then "FizzBuzz"
  else if n % 3 == 0 then "Fizz"
  else if n % 5 == 0 then "Buzz"
  else toString n

-- ============================================
-- FizzBuzz の性質を証明する
-- ============================================

-- 15の倍数なら必ず "FizzBuzz" を返す
theorem fizzbuzz_of_mul_15 (k : Nat) : fizzbuzz (15 * (k + 1)) = "FizzBuzz" := by
  simp [fizzbuzz]

-- 3の倍数で15の倍数でないなら "Fizz"
theorem fizzbuzz_fizz (n : Nat)
    (h15 : (n % 15 == 0) = false) (h3 : (n % 3 == 0) = true) :
    fizzbuzz n = "Fizz" := by
  simp [fizzbuzz, h15, h3]

-- 5の倍数で3の倍数でないなら "Buzz"
theorem fizzbuzz_buzz (n : Nat)
    (h15 : (n % 15 == 0) = false) (h3 : (n % 3 == 0) = false)
    (h5 : (n % 5 == 0) = true) :
    fizzbuzz n = "Buzz" := by
  simp [fizzbuzz, h15, h3, h5]

-- fizzbuzz の結果は4パターンしかない
theorem fizzbuzz_cases (n : Nat) :
    fizzbuzz n = "FizzBuzz" ∨ fizzbuzz n = "Fizz" ∨
    fizzbuzz n = "Buzz" ∨ fizzbuzz n = toString n := by
  unfold fizzbuzz
  split
  · left; rfl
  · split
    · right; left; rfl
    · split
      · right; right; left; rfl
      · right; right; right; rfl

-- 具体例も decide で一発証明
theorem fizzbuzz_15_eq : fizzbuzz 15 = "FizzBuzz" := by decide
theorem fizzbuzz_9_eq  : fizzbuzz 9  = "Fizz"     := by decide
theorem fizzbuzz_20_eq : fizzbuzz 20 = "Buzz"     := by decide
theorem fizzbuzz_7_eq  : fizzbuzz 7  = "7"        := by decide
