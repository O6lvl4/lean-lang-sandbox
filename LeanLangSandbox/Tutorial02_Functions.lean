-- ============================================
-- Lean 4 関数チュートリアル
-- 他言語経験者のための関数プログラミング入門
-- ============================================
-- このファイルは単体でコンパイルできます。
-- #eval で結果を確認しながら読み進めてください。
--
-- 注意: 他のチュートリアルファイルとの名前衝突を避けるため
-- namespace Tutorial02 で囲んでいます。

namespace Tutorial02

-- ============================================
-- 1. 名前付き関数 (def)
-- ============================================
-- Lean では `def` キーワードで関数を定義する。
-- 型注釈は `: 戻り値の型` で書く。引数の型は `(引数名 : 型)` で指定する。

-- 最もシンプルな関数: 引数を2倍にする
def double (n : Nat) : Nat :=
  n * 2

#eval double 5      -- 10
#eval double 0      -- 0
#eval double 100    -- 200

-- 文字列を受け取って挨拶を返す関数
-- `++` は文字列の結合演算子（他言語の `+` に相当）
def greet (name : String) : String :=
  "こんにちは、" ++ name ++ "さん！"

#eval greet "太郎"   -- "こんにちは、太郎さん！"

-- Bool を返す関数
-- Lean の自然数 (Nat) は 0 以上なので、負数はない
def isEven (n : Nat) : Bool :=
  n % 2 == 0

#eval isEven 4    -- true
#eval isEven 7    -- false

-- if 式を使った関数
-- Lean の if は「式」なので値を返す（三項演算子のようなもの）
def myAbs (n : Int) : Int :=
  if n < 0 then -n else n

#eval myAbs (-42)   -- 42
#eval myAbs 10      -- 10

-- match 式を使ったパターンマッチ
-- 他言語の switch/case に近いが、もっと強力
def describe (n : Nat) : String :=
  match n with
  | 0 => "ゼロ"
  | 1 => "いち"
  | 2 => "に"
  | _ => "たくさん"    -- `_` はワイルドカード（それ以外全部）

#eval describe 0    -- "ゼロ"
#eval describe 1    -- "いち"
#eval describe 99   -- "たくさん"


-- ============================================
-- 2. 無名関数 (fun / ラムダ式)
-- ============================================
-- `fun` キーワードでその場で関数を作れる。
-- 他言語の arrow function (=>) や lambda に相当する。
-- Lean では `fun 引数 => 本体` と書く。

-- 無名関数をそのまま #eval で使う
#eval (fun x => x + 1) 10           -- 11
#eval (fun x => x * x) 7            -- 49
#eval (fun s => s ++ "!") "hello"   -- "hello!"

-- 無名関数を変数に束縛する（def と実質同じ）
def addOne : Nat → Nat :=
  fun x => x + 1

#eval addOne 5    -- 6

-- 複数引数の無名関数
#eval (fun x y => x + y) 3 4    -- 7

-- 型注釈付きの無名関数
-- 必要に応じて引数の型を明示できる
#eval (fun (x : Nat) (y : Nat) => x * y + 1) 3 4   -- 13

-- ラムダ式のネスト: fun x => fun y => ... と書いてもよい
-- 実は `fun x y => ...` は `fun x => fun y => ...` の省略形
#eval (fun x => fun y => x + y) 10 20   -- 30


-- ============================================
-- 3. 複数引数とカリー化
-- ============================================
-- Lean の関数は自動的に「カリー化」されている。
-- つまり、複数引数の関数は「1引数の関数を返す関数」として扱われる。
--
-- 例: add : Nat → Nat → Nat
-- これは実際には Nat → (Nat → Nat) と同じ意味。
-- 「Nat を受け取って、Nat → Nat な関数を返す関数」

def add (x : Nat) (y : Nat) : Nat :=
  x + y

#eval add 3 5      -- 8

-- `add 3` は「3を足す関数」を返す（部分適用、次のセクションで詳しく）
-- 型を確認: add 3 の型は Nat → Nat
#check add 3       -- add 3 : Nat → Nat

-- 3引数の関数
def addThree (x y z : Nat) : Nat :=
  x + y + z

-- 同じ型の引数はまとめて書ける: (x y z : Nat) は (x : Nat) (y : Nat) (z : Nat) の省略
#eval addThree 1 2 3    -- 6

-- 異なる型の引数を取る関数
def repeatStr (s : String) (n : Nat) : String :=
  match n with
  | 0 => ""
  | n + 1 => s ++ repeatStr s n

#eval repeatStr "ha" 3    -- "hahaha"
#eval repeatStr "!" 5     -- "!!!!!"


-- ============================================
-- 4. 部分適用
-- ============================================
-- カリー化のおかげで、引数を一部だけ渡して新しい関数を作れる。
-- これを「部分適用」(partial application) という。

-- add に 10 だけ渡すと「10を足す関数」ができる
def add10 : Nat → Nat := add 10

#eval add10 5      -- 15
#eval add10 0      -- 10
#eval add10 100    -- 110

-- repeatStr に "***" だけ渡すと「"***" を n 回繰り返す関数」になる
def stars : Nat → String := repeatStr "***"

#eval stars 3    -- "*********"

-- 掛け算の部分適用
def multiply (x y : Nat) : Nat := x * y

def triple : Nat → Nat := multiply 3

#eval triple 7     -- 21
#eval triple 10    -- 30

-- リスト操作と組み合わせると部分適用は特に便利（後述の高階関数セクション参照）
#eval [1, 2, 3, 4, 5].map (add 100)    -- [101, 102, 103, 104, 105]
#eval [1, 2, 3, 4, 5].map (multiply 2) -- [2, 4, 6, 8, 10]


-- ============================================
-- 5. where 句
-- ============================================
-- `where` を使うと、関数本体の後にローカル定義を書ける。
-- 「まず結論を書いて、細部は後で」というトップダウンのスタイル。
-- 他言語の内部関数やローカル変数に近い。

-- 円の面積を計算（整数近似版）
def circleArea (radius : Nat) : Nat :=
  piApprox * radius * radius
  where
    -- ローカル定義: この関数内でだけ使える
    piApprox := 3  -- 本当は 3.14159... だが整数で近似

#eval circleArea 10    -- 300

-- BMI 計算（整数近似版）
-- where で複数のローカル関数・値を定義できる
def bmiCategory (weightKg : Nat) (heightCm : Nat) : String :=
  if bmi < 185 then "やせ"
  else if bmi < 250 then "普通"
  else if bmi < 300 then "肥満1度"
  else "肥満2度以上"
  where
    -- BMI = 体重(kg) / 身長(m)^2 を整数 (x10) で近似
    bmi := weightKg * 100000 / (heightCm * heightCm)

#eval bmiCategory 60 170    -- "普通"

-- where の中で関数も定義できる
def formatList (xs : List Nat) : String :=
  "[" ++ joinItems ", " (xs.map toString) ++ "]"
  where
    joinItems (sep : String) : List String → String
      | [] => ""
      | [x] => x
      | x :: xs => x ++ sep ++ joinItems sep xs

#eval formatList [1, 2, 3, 4, 5]    -- "[1, 2, 3, 4, 5]"
#eval formatList []                  -- "[]"

-- let ... in ... でもローカル定義できる（where の代替）
-- where はトップダウン、let はボトムアップのスタイル
def hypotenuseSquared (a b : Nat) : Nat :=
  let aSquared := a * a
  let bSquared := b * b
  -- 本当は平方根を取るべきだが、二乗和を返す簡易版
  aSquared + bSquared

#eval hypotenuseSquared 3 4    -- 25 （本当は √25 = 5）


-- ============================================
-- 6. デフォルト引数と名前付き引数
-- ============================================
-- Lean ではデフォルト値付きの引数を定義できる。
-- 呼び出し時に省略するとデフォルト値が使われる。

-- デフォルト引数の例: sep のデフォルトは ", "
def joinStrings (xs : List String) (sep : String := ", ") : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ joinStrings rest sep

#eval joinStrings ["a", "b", "c"]          -- "a, b, c"   （デフォルトの ", " を使用）
#eval joinStrings ["a", "b", "c"] " - "    -- "a - b - c" （sep を指定）
#eval joinStrings ["a", "b", "c"] "/"      -- "a/b/c"

-- 名前付き引数で呼び出す
-- 引数の順番を変えたい場合や、可読性を上げたい場合に便利
#eval joinStrings (sep := " | ") (xs := ["x", "y", "z"])   -- "x | y | z"

-- 複数のデフォルト引数
def makeGreeting
    (name : String)
    (greetPrefix : String := "こんにちは")
    (suffix : String := "！") : String :=
  greetPrefix ++ "、" ++ name ++ "さん" ++ suffix

#eval makeGreeting "花子"                              -- "こんにちは、花子さん！"
#eval makeGreeting "花子" "おはよう"                    -- "おはよう、花子さん！"
#eval makeGreeting "花子" "おはよう" "。"               -- "おはよう、花子さん。"
-- 名前付き引数でsuffixだけ変更（greetPrefixはデフォルトのまま）
#eval makeGreeting "花子" (suffix := "。元気？")        -- "こんにちは、花子さん。元気？"

-- オートバウンド暗黙引数 (autobound implicit)
-- 型変数を明示的に宣言しなくても、Lean が自動で推論してくれる
-- 以下の `α` は自動的に暗黙引数 `{α : Type}` になる
def listLength (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: rest => 1 + listLength rest

#eval listLength [1, 2, 3]          -- 3
#eval listLength ["a", "b"]         -- 2
#eval listLength ([] : List Nat)    -- 0


-- ============================================
-- 7. 高階関数 (関数を受け取る関数)
-- ============================================
-- 「関数を引数として受け取る関数」を高階関数 (higher-order function) という。
-- 関数型プログラミングの真骨頂。
-- map, filter, fold などが代表例。

-- 自作の map: リストの各要素に関数 f を適用する
def myMap (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: myMap f xs

#eval myMap (fun x => x * 2) [1, 2, 3, 4]    -- [2, 4, 6, 8]
#eval myMap (fun s => s ++ "!") ["hi", "hey"] -- ["hi!", "hey!"]
#eval myMap double [10, 20, 30]               -- [20, 40, 60]

-- 自作の filter: 条件を満たす要素だけ残す
def myFilter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then x :: myFilter p xs
    else myFilter p xs

#eval myFilter isEven [1, 2, 3, 4, 5, 6]           -- [2, 4, 6]
#eval myFilter (fun n => n > 3) [1, 2, 3, 4, 5]    -- [4, 5]

-- 自作の foldl: リストを左から畳み込む
-- 他言語の reduce に相当
-- foldl f init [a, b, c] = f (f (f init a) b) c
def myFoldl (f : β → α → β) (init : β) : List α → β
  | [] => init
  | x :: xs => myFoldl f (f init x) xs

-- リストの合計
#eval myFoldl (fun acc x => acc + x) 0 [1, 2, 3, 4, 5]    -- 15

-- リストの最大値
#eval myFoldl (fun acc x => if x > acc then x else acc) 0 [3, 1, 4, 1, 5, 9, 2, 6]  -- 9

-- 関数を2回適用する高階関数
def applyTwice (f : α → α) (x : α) : α :=
  f (f x)

#eval applyTwice (fun x => x + 3) 10     -- 16  (10 -> 13 -> 16)
#eval applyTwice (fun x => x * 2) 1      -- 4   (1 -> 2 -> 4)
#eval applyTwice (fun s => "(" ++ s ++ ")") "hi"  -- "((hi))"

-- 関数を n 回適用する
def applyN (f : α → α) (n : Nat) (x : α) : α :=
  match n with
  | 0 => x
  | n + 1 => applyN f n (f x)

#eval applyN (fun x => x + 1) 5 0     -- 5
#eval applyN (fun x => x * 2) 10 1    -- 1024

-- 標準ライブラリの高階関数を使う
#eval [1, 2, 3, 4, 5].map (· * 10)              -- [10, 20, 30, 40, 50]
-- `·` はプレースホルダ記法。`fun x => x * 10` の省略形
#eval [1, 2, 3, 4, 5].filter (· > 3)            -- [4, 5]
#eval [1, 2, 3, 4, 5].foldl (· + ·) 0           -- 15
-- `· + ·` は `fun a b => a + b` の省略形

-- any: いずれかの要素が条件を満たすか
#eval [1, 2, 3, 4, 5].any (· > 4)    -- true
#eval [1, 2, 3].any (· > 10)         -- false

-- all: すべての要素が条件を満たすか
#eval [2, 4, 6].all isEven            -- true
#eval [2, 4, 5].all isEven            -- false


-- ============================================
-- 8. 関数合成
-- ============================================
-- 関数合成は「2つの関数を組み合わせて新しい関数を作る」こと。
-- 数学の f . g (f composed with g) に対応する。
-- Lean では `f ∘ g` または `Function.comp f g` と書く。
-- (f ∘ g) x = f (g x) という意味。

-- double してから addOne する合成関数
def doubleAndAddOne : Nat → Nat := addOne ∘ double
-- 注意: `addOne ∘ double` は「まず double、次に addOne」の順
-- 数学の記法と同じで、右から左に適用される

#eval doubleAndAddOne 5     -- 11  (5 -> 10 -> 11)
#eval doubleAndAddOne 0     -- 1   (0 -> 0  -> 1)

-- 合成を連鎖させる
def tripleProcess : Nat → Nat := addOne ∘ double ∘ add 3
-- add 3 -> double -> addOne の順に適用

#eval tripleProcess 2    -- 11  (2 -> 5 -> 10 -> 11)
#eval tripleProcess 10   -- 27  (10 -> 13 -> 26 -> 27)

-- パイプライン演算子 `|>` で左から右に書くこともできる
-- 他言語のメソッドチェーンに近い感覚
#eval 5 |> double |> addOne              -- 11
#eval 2 |> add 3 |> double |> addOne     -- 11

-- `<|` は逆向き（右から左）のパイプライン
-- 括弧を減らすために使う
#eval addOne <| double <| add 3 <| 2     -- 11

-- 自作の関数合成
def compose (f : β → γ) (g : α → β) : α → γ :=
  fun x => f (g x)

def isEvenAfterDouble : Nat → Bool := compose isEven double

#eval isEvenAfterDouble 3    -- true  (3 -> 6 -> true)
#eval isEvenAfterDouble 5    -- true  (5 -> 10 -> true)
-- double の結果は常に偶数なので、常に true


-- ============================================
-- 9. 再帰関数と停止性証明
-- ============================================
-- Lean は全関数 (total function) を要求する。
-- つまり、すべての再帰関数は必ず停止することを証明しなければならない。
-- 多くの場合、Lean が自動で停止性を証明してくれる。
-- 自然数のパターンマッチ `n + 1` を使えば、n が減少することを Lean は理解する。

-- ----- 階乗 (factorial) -----
-- n! = 1 * 2 * ... * n
-- 0! = 1, n! = n * (n-1)! と再帰的に定義
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
  -- Lean は `n < n + 1` を自動で認識し、停止性を証明する

#eval factorial 0     -- 1
#eval factorial 1     -- 1
#eval factorial 5     -- 120
#eval factorial 10    -- 3628800
#eval factorial 20    -- 2432902008176640000

-- 末尾再帰版の階乗（大きな入力でスタックオーバーフローしない）
-- アキュムレータ (acc) パターンを使う
def factorialTR (n : Nat) : Nat :=
  go n 1
  where
    go : Nat → Nat → Nat
      | 0, acc => acc
      | n + 1, acc => go n ((n + 1) * acc)

#eval factorialTR 20    -- 2432902008176640000

-- ----- フィボナッチ数列 -----
-- fib(0) = 0, fib(1) = 1, fib(n) = fib(n-1) + fib(n-2)
-- 素朴な再帰版（指数的に遅い！ n > 30 あたりで実用的でなくなる）
def fibSlow : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSlow (n + 1) + fibSlow n

#eval fibSlow 0     -- 0
#eval fibSlow 1     -- 1
#eval fibSlow 10    -- 55
#eval fibSlow 20    -- 6765

-- 効率的なフィボナッチ（末尾再帰 + アキュムレータ）
-- O(n) で計算できる
def fib (n : Nat) : Nat :=
  go n 0 1
  where
    go : Nat → Nat → Nat → Nat
      | 0, a, _ => a
      | n + 1, a, b => go n b (a + b)
      -- a = fib(k), b = fib(k+1) を保持しながらループ

#eval fib 0      -- 0
#eval fib 1      -- 1
#eval fib 10     -- 55
#eval fib 50     -- 12586269025
#eval fib 100    -- 354224848179261915075

-- ----- べき乗 (power) -----
-- base ^ exp を計算する
def power (base : Nat) : Nat → Nat
  | 0 => 1                              -- x^0 = 1
  | n + 1 => base * power base n        -- x^(n+1) = x * x^n

#eval power 2 0     -- 1
#eval power 2 10    -- 1024
#eval power 3 5     -- 243
#eval power 10 6    -- 1000000

-- 高速べき乗（繰り返し二乗法）
-- O(log n) で計算できる。暗号などで重要なアルゴリズム。
-- n が偶数なら (base^(n/2))^2、奇数なら base * base^(n-1) を使う
partial def fastPower (base : Nat) (exp : Nat) : Nat :=
  if exp == 0 then 1
  else if exp % 2 == 0 then
    let half := fastPower base (exp / 2)
    half * half
  else
    base * fastPower base (exp - 1)

#eval fastPower 2 10     -- 1024
#eval fastPower 2 20     -- 1048576
#eval fastPower 3 10     -- 59049

-- ----- 最大公約数 (GCD) -----
-- ユークリッドの互除法
-- gcd(a, 0) = a
-- gcd(a, b) = gcd(b, a % b)
partial def gcd (a b : Nat) : Nat :=
  if b == 0 then a
  else gcd b (a % b)

#eval gcd 12 8      -- 4
#eval gcd 100 75    -- 25
#eval gcd 17 13     -- 1  （互いに素）
#eval gcd 0 5       -- 5
#eval gcd 48 18     -- 6

-- 最小公倍数 (LCM) は GCD を使って計算できる
-- lcm(a, b) = a * b / gcd(a, b)
def lcm (a b : Nat) : Nat :=
  if a == 0 || b == 0 then 0
  else a * b / gcd a b

#eval lcm 4 6       -- 12
#eval lcm 12 18     -- 36
#eval lcm 7 5       -- 35

-- ----- コラッツ予想のステップ数 -----
-- n が 1 になるまでのステップ数を数える
-- n が偶数なら n/2、奇数なら 3n+1
-- (停止性は未証明だが、partial で「証明しない」と宣言できる)
partial def collatzSteps : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)
  -- `partial` は「この関数は停止しないかもしれない」という宣言
  -- 実用上は問題ないが、Lean の証明には使えなくなる

#eval collatzSteps 1      -- 0
#eval collatzSteps 6      -- 8    (6->3->10->5->16->8->4->2->1)
#eval collatzSteps 27     -- 111  （27 は意外と長い）


-- ============================================
-- 10. まとめ: 総合演習
-- ============================================

-- リストの各要素を2乗してから偶数だけフィルタリングし、合計を求める
def sumOfEvenSquares (xs : List Nat) : Nat :=
  xs.map (fun x => x * x)     -- 各要素を2乗
    |>.filter isEven           -- 偶数だけ残す
    |>.foldl (· + ·) 0        -- 合計を求める

#eval sumOfEvenSquares [1, 2, 3, 4, 5]    -- 4 + 16 = 20
#eval sumOfEvenSquares [1, 3, 5, 7]       -- 0（奇数の2乗は奇数）
#eval sumOfEvenSquares [2, 4, 6]          -- 4 + 16 + 36 = 56

-- 関数のリストを順に適用するパイプライン
def pipeline (fs : List (α → α)) (x : α) : α :=
  fs.foldl (fun acc f => f acc) x

#eval pipeline [double, addOne, triple] 5
  -- 5 -> 10 -> 11 -> 33

-- 数値リストの統計情報を文字列で返す
def stats (xs : List Nat) : String :=
  s!"個数: {count}, 合計: {total}, 最大: {maxVal}"
  where
    count := xs.length
    total := xs.foldl (· + ·) 0
    maxVal := xs.foldl (fun acc x => if x > acc then x else acc) 0

#eval stats [3, 1, 4, 1, 5, 9, 2, 6]
  -- "個数: 8, 合計: 31, 最大: 9"

-- 関数を組み合わせて FizzBuzz を実装（高階関数の応用）
def fizzBuzz (n : Nat) : String :=
  let rules := [
    (fun i => if i % 15 == 0 then some "FizzBuzz" else none),
    (fun i => if i % 3 == 0 then some "Fizz" else none),
    (fun i => if i % 5 == 0 then some "Buzz" else none)
  ]
  applyRules rules n
  where
    applyRules : List (Nat → Option String) → Nat → String
      | [], n => toString n
      | f :: fs, n =>
        match f n with
        | some s => s
        | none => applyRules fs n

#eval (List.range 16).map (fun i => fizzBuzz (i + 1))
  -- ["1", "2", "Fizz", "4", "Buzz", "Fizz", "7", "8", "Fizz", "Buzz",
  --  "11", "Fizz", "13", "14", "FizzBuzz", "16"]

end Tutorial02
