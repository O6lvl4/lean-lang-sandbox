import LeanLangSandbox

def main : IO Unit := do
  for i in List.range 30 do
    IO.println (fizzbuzz (i + 1))
