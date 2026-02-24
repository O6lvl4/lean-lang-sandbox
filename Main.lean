import LeanLangSandbox

def main : IO Unit := do
  -- FizzBuzz
  for i in List.range 30 do
    IO.println (fizzbuzz (i + 1))
  -- Project Euler
  IO.println ""
  IO.println s!"Project Euler Problem 0: {ProjectEuler.sumOddSquaresFormula 510000}"
  IO.println s!"Project Euler Problem 1: {ProjectEuler1.sumMultiples3or5Formula 1000}"
  IO.println s!"Project Euler Problem 2: {ProjectEuler2.sumEvenFib 4000000}"
