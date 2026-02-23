-- ============================================
-- Tutorial 03: パターンマッチ完全ガイド
-- 他言語経験者のための Lean 4 パターンマッチ入門
-- ============================================
-- パターンマッチは Lean 4 の最も強力な機能の一つ。
-- C/Java の switch 文を遥かに超える表現力を持つ。
-- しかも「全ケース網羅」をコンパイラが保証してくれる。

namespace Tutorial03

-- ============================================
-- 1. match 式の基本
-- ============================================
-- 他言語の switch/case に相当するが、はるかに強力。
-- 構文: match 対象 with | パターン1 => 式1 | パターン2 => 式2

-- まずは一番シンプルな例: 数値の判定
def describeNat (n : Nat) : String :=
  match n with
  | 0 => "ゼロ"
  | 1 => "いち"
  | 2 => "に"
  | _ => "それ以外"  -- _ はワイルドカード（後述）

#eval describeNat 0    -- "ゼロ"
#eval describeNat 1    -- "いち"
#eval describeNat 2    -- "に"
#eval describeNat 42   -- "それ以外"

-- ============================================
-- 2. Nat のパターンマッチ: zero と succ
-- ============================================
-- Lean の Nat（自然数）は帰納型として定義されている:
--   inductive Nat where
--     | zero : Nat          -- 0
--     | succ (n : Nat) : Nat  -- n + 1
--
-- つまり 3 = succ (succ (succ zero))
-- この構造に対してパターンマッチできるのが Lean の強み。

-- 自然数が 0 かどうか判定
def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true          -- Nat.zero のこと
  | _ + 1 => false     -- Nat.succ _ のこと

#eval isZero 0   -- true
#eval isZero 1   -- false
#eval isZero 99  -- false

-- succ パターンで前の数を取り出す
-- n + 1 というパターンで、n に「1つ前の数」が束縛される
def predecessor (n : Nat) : Nat :=
  match n with
  | 0 => 0            -- 0 の前は 0（自然数なので負にならない）
  | n + 1 => n        -- succ n のとき、n を返す

#eval predecessor 0   -- 0
#eval predecessor 1   -- 0
#eval predecessor 5   -- 4
#eval predecessor 100 -- 99

-- 再帰とパターンマッチの組み合わせ: 階乗
-- これが関数型プログラミングの基本パターン
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 0   -- 1
#eval factorial 1   -- 1
#eval factorial 5   -- 120
#eval factorial 10  -- 3628800

-- フィボナッチ数列（2つのパターンで再帰）
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib 0   -- 0
#eval fib 1   -- 1
#eval fib 2   -- 1
#eval fib 10  -- 55

-- ============================================
-- 3. Bool のパターンマッチ
-- ============================================
-- Bool は true / false の2値。パターンマッチの最もシンプルな例。

def boolToJapanese (b : Bool) : String :=
  match b with
  | true  => "真"
  | false => "偽"

#eval boolToJapanese true   -- "真"
#eval boolToJapanese false  -- "偽"

-- Bool の否定を自作（notと同じ）
def myNot : Bool → Bool
  | true  => false
  | false => true

#eval myNot true   -- false
#eval myNot false  -- true

-- Bool の AND を自作
def myAnd : Bool → Bool → Bool
  | true,  b => b       -- true AND b = b
  | false, _ => false   -- false AND anything = false

#eval myAnd true true    -- true
#eval myAnd true false   -- false
#eval myAnd false true   -- false
#eval myAnd false false  -- false

-- ============================================
-- 4. タプル（組）のパターンマッチ
-- ============================================
-- タプルは (a, b) の形で、複数の値をまとめたもの。
-- パターンマッチで各要素を取り出せる。

-- ペア（2つ組）の要素を入れ替える
def swap (pair : Nat × String) : String × Nat :=
  match pair with
  | (n, s) => (s, n)

#eval swap (42, "hello")  -- ("hello", 42)

-- ペアの両方の要素を取り出して処理
def describePair (pair : Nat × Nat) : String :=
  match pair with
  | (0, 0) => "両方ゼロ"
  | (0, _) => "左だけゼロ"
  | (_, 0) => "右だけゼロ"
  | (a, b) => s!"左={a}, 右={b}"

#eval describePair (0, 0)   -- "両方ゼロ"
#eval describePair (0, 5)   -- "左だけゼロ"
#eval describePair (3, 0)   -- "右だけゼロ"
#eval describePair (3, 7)   -- "左=3, 右=7"

-- 3つ組のパターンマッチ
def describeTriple (t : Nat × Nat × Nat) : String :=
  match t with
  | (0, 0, 0) => "全部ゼロ"
  | (a, b, c) => s!"合計={a + b + c}"

#eval describeTriple (0, 0, 0)  -- "全部ゼロ"
#eval describeTriple (1, 2, 3)  -- "合計=6"

-- ============================================
-- 5. ネストしたパターン
-- ============================================
-- パターンは入れ子にできる。これが強力すぎる。
-- C/Java では条件分岐のネストが深くなるところを、フラットに書ける。

-- Option 型のネスト: Option の中に Option
-- Option α は「値があるかもしれない」型
--   some x : 値 x がある
--   none   : 値がない
def describeNestedOption (x : Option (Option Nat)) : String :=
  match x with
  | none          => "外側がnone"
  | some none     => "外側はsome、中身がnone"
  | some (some n) => s!"値は{n}"

#eval describeNestedOption none              -- "外側がnone"
#eval describeNestedOption (some none)       -- "外側はsome、中身がnone"
#eval describeNestedOption (some (some 42))  -- "値は42"

-- リストの先頭パターン
-- List は [] (空) または x :: xs (先頭 :: 残り) で構成される
def describeList (xs : List Nat) : String :=
  match xs with
  | []           => "空リスト"
  | [x]          => s!"要素1つ: {x}"
  | [x, y]       => s!"要素2つ: {x}, {y}"
  | x :: y :: _  => s!"3つ以上: 先頭={x}, 2番目={y}"

#eval describeList []           -- "空リスト"
#eval describeList [10]         -- "要素1つ: 10"
#eval describeList [10, 20]     -- "要素2つ: 10, 20"
#eval describeList [10, 20, 30] -- "3つ以上: 先頭=10, 2番目=20"

-- Nat と List のネスト: リストの先頭が 0 かどうかも同時に判定
def headIsZero (xs : List Nat) : String :=
  match xs with
  | []      => "空リスト"
  | 0 :: _  => "先頭がゼロ"
  | _ :: _  => "先頭がゼロ以外"

#eval headIsZero []        -- "空リスト"
#eval headIsZero [0, 1, 2] -- "先頭がゼロ"
#eval headIsZero [5, 1, 2] -- "先頭がゼロ以外"

-- ============================================
-- 6. ワイルドカード _ パターン
-- ============================================
-- _ は「何でもマッチするが、値を使わない」ときに使う。
-- 他言語の default: に近いが、もっと柔軟。

-- 値に興味がないとき
def isOne (n : Nat) : Bool :=
  match n with
  | 1 => true
  | _ => false   -- 0でも2でも100でもここに来る

#eval isOne 1   -- true
#eval isOne 0   -- false
#eval isOne 99  -- false

-- タプルの一部だけ取り出す
def getFirst (pair : Nat × String) : Nat :=
  match pair with
  | (n, _) => n   -- 2番目の要素は使わないので _

#eval getFirst (42, "hello")  -- 42

-- 複数の _ を組み合わせる
def middleOfThree (t : Nat × Nat × Nat) : Nat :=
  match t with
  | (_, m, _) => m   -- 真ん中だけ取り出す

#eval middleOfThree (1, 2, 3)  -- 2

-- ============================================
-- 7. 複数パターンを1つのアームにまとめる（| を使う）
-- ============================================
-- 同じ結果になるパターンをまとめて書ける。
-- C/Java の case A: case B: のフォールスルーに似ているが、
-- 意図が明確で安全。

-- 母音判定
def isVowel (c : Char) : Bool :=
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' => true
  | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

#eval isVowel 'a'  -- true
#eval isVowel 'E'  -- true
#eval isVowel 'x'  -- false

-- 数字を「小さい」「中くらい」「大きい」に分類
def sizeCategory (n : Nat) : String :=
  match n with
  | 0 | 1 | 2       => "小さい"
  | 3 | 4 | 5       => "中くらい"
  | _               => "大きい"

#eval sizeCategory 0   -- "小さい"
#eval sizeCategory 2   -- "小さい"
#eval sizeCategory 4   -- "中くらい"
#eval sizeCategory 99  -- "大きい"

-- Bool の or を | パターンで書く
-- 注意: | パターン内で変数を束縛する場合、
-- すべての選択肢で同じ変数を束縛する必要がある
def isTrue (b : Bool) : String :=
  match b with
  | true  => "真です"
  | false => "偽です"

-- ============================================
-- 8. ガード（if を使った条件付きパターン）
-- ============================================
-- Lean 4 には Haskell のような直接的なガード構文はないが、
-- match の中で if を使って同等のことができる。

-- 方法1: パターンマッチの中で if を使う
def classifyAge (age : Nat) : String :=
  match age with
  | 0 => "赤ちゃん"
  | n => if n < 6 then "幼児"
         else if n < 13 then "子供"
         else if n < 18 then "ティーン"
         else if n < 65 then "大人"
         else "シニア"

#eval classifyAge 0   -- "赤ちゃん"
#eval classifyAge 3   -- "幼児"
#eval classifyAge 10  -- "子供"
#eval classifyAge 15  -- "ティーン"
#eval classifyAge 30  -- "大人"
#eval classifyAge 70  -- "シニア"

-- 方法2: パターン + 条件の組み合わせ
-- リストの要素を条件付きで処理
def describeFirst (xs : List Nat) : String :=
  match xs with
  | []     => "空"
  | x :: _ => if x == 0 then "先頭が0"
              else if x > 100 then "先頭が100超"
              else s!"先頭は{x}"

#eval describeFirst []       -- "空"
#eval describeFirst [0, 1]   -- "先頭が0"
#eval describeFirst [200]    -- "先頭が100超"
#eval describeFirst [42, 10] -- "先頭は42"

-- パターンマッチ + ガードで FizzBuzz を書く
def fizzBuzzMatch (n : Nat) : String :=
  match n % 3, n % 5 with
  | 0, 0 => "FizzBuzz"   -- 3でも5でも割り切れる
  | 0, _ => "Fizz"       -- 3だけで割り切れる
  | _, 0 => "Buzz"       -- 5だけで割り切れる
  | _, _ => toString n   -- どちらでも割り切れない

#eval fizzBuzzMatch 15  -- "FizzBuzz"
#eval fizzBuzzMatch 9   -- "Fizz"
#eval fizzBuzzMatch 20  -- "Buzz"
#eval fizzBuzzMatch 7   -- "7"

-- ============================================
-- 9. 網羅性（Exhaustiveness）
-- ============================================
-- Lean はパターンマッチが全ケースを網羅しているかチェックする。
-- これは他言語にはない（あっても警告レベルの）強力な安全機能。
--
-- 例えば、以下のコードはコンパイルエラーになる:
--
-- def broken (b : Bool) : String :=
--   match b with
--   | true => "真"
--   -- false のケースがない！ → コンパイルエラー
--
-- エラーメッセージ:
--   missing cases:
--     | false
--
-- これにより「想定外のケースを忘れる」バグを防げる。
-- TypeScript の switch で default を書き忘れるような事故が起きない。

-- 正しい網羅的パターンマッチの例:
def safeMatch (b : Bool) : String :=
  match b with
  | true  => "真"
  | false => "偽"
  -- 全ケース網羅 → コンパイル通る

-- Option型も網羅が必要
def unwrapOrDefault (x : Option Nat) : Nat :=
  match x with
  | some n => n
  | none   => 0
  -- some と none の両方を処理 → OK

#eval unwrapOrDefault (some 42)  -- 42
#eval unwrapOrDefault none       -- 0

-- Nat は無限にケースがあるが、0 と succ n で網羅できる
-- これは Nat が inductive 型で zero | succ n の2つのコンストラクタだけだから
def isEvenSimple : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => isEvenSimple n

#eval isEvenSimple 0   -- true
#eval isEvenSimple 3   -- false
#eval isEvenSimple 10  -- true

-- ============================================
-- 10. 実践例: 曜日
-- ============================================
-- 独自の列挙型を定義してパターンマッチ

-- 曜日を表す型
inductive DayOfWeek where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr  -- #eval で表示するために必要

open DayOfWeek  -- 名前空間を開く（DayOfWeek.monday を monday と書ける）

-- 平日か週末か判定
def isWeekend : DayOfWeek → Bool
  | saturday => true
  | sunday   => true
  | _        => false   -- 残り5日は全部平日

#eval isWeekend monday    -- false
#eval isWeekend saturday  -- true
#eval isWeekend sunday    -- true

-- 曜日を日本語に変換
def dayToJapanese : DayOfWeek → String
  | monday    => "月曜日"
  | tuesday   => "火曜日"
  | wednesday => "水曜日"
  | thursday  => "木曜日"
  | friday    => "金曜日"
  | saturday  => "土曜日"
  | sunday    => "日曜日"

#eval dayToJapanese monday     -- "月曜日"
#eval dayToJapanese friday     -- "金曜日"
#eval dayToJapanese sunday     -- "日曜日"

-- 次の曜日を返す
def nextDay : DayOfWeek → DayOfWeek
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday

#eval dayToJapanese (nextDay friday)  -- "土曜日"
#eval dayToJapanese (nextDay sunday)  -- "月曜日"

-- 平日なら「あと何日で週末？」
def daysUntilWeekend : DayOfWeek → Nat
  | monday    => 5
  | tuesday   => 4
  | wednesday => 3
  | thursday  => 2
  | friday    => 1
  | saturday  => 0
  | sunday    => 0

#eval daysUntilWeekend monday    -- 5
#eval daysUntilWeekend thursday  -- 2
#eval daysUntilWeekend saturday  -- 0

-- ============================================
-- 11. 実践例: 信号機
-- ============================================

inductive TrafficLight where
  | red
  | yellow
  | green
  deriving Repr

open TrafficLight in
def lightAction : TrafficLight → String
  | red    => "止まれ"
  | yellow => "注意して進め"
  | green  => "進め"

#eval lightAction TrafficLight.red     -- "止まれ"
#eval lightAction TrafficLight.yellow  -- "注意して進め"
#eval lightAction TrafficLight.green   -- "進め"

-- 次の信号を返す（赤→緑→黄→赤→...）
open TrafficLight in
def nextLight : TrafficLight → TrafficLight
  | red    => green
  | green  => yellow
  | yellow => red

#eval lightAction (nextLight TrafficLight.red)    -- "進め"  (赤の次は緑)
#eval lightAction (nextLight TrafficLight.green)  -- "注意して進め" (緑の次は黄)
#eval lightAction (nextLight TrafficLight.yellow) -- "止まれ" (黄の次は赤)

-- ============================================
-- 12. 実践例: 簡易電卓
-- ============================================
-- 四則演算をパターンマッチで処理する

-- 演算子を表す型
inductive Op where
  | add
  | sub
  | mul
  | div
  deriving Repr

-- 演算を実行する関数
-- 結果は Option Int: 0除算のとき none を返す
def calculate (op : Op) (a b : Int) : Option Int :=
  match op with
  | Op.add => some (a + b)
  | Op.sub => some (a - b)
  | Op.mul => some (a * b)
  | Op.div => if b == 0 then none else some (a / b)

#eval calculate Op.add 10 3   -- some 13
#eval calculate Op.sub 10 3   -- some 7
#eval calculate Op.mul 10 3   -- some 30
#eval calculate Op.div 10 3   -- some 3
#eval calculate Op.div 10 0   -- none （0除算は安全にnone）

-- 結果を文字列にフォーマット
def formatResult (result : Option Int) : String :=
  match result with
  | some n => s!"結果: {n}"
  | none   => "エラー: 0で割ることはできません"

#eval formatResult (calculate Op.add 10 3)  -- "結果: 13"
#eval formatResult (calculate Op.div 10 0)  -- "エラー: 0で割ることはできません"

-- 演算子のシンボルを返す
def opSymbol : Op → String
  | Op.add => "+"
  | Op.sub => "-"
  | Op.mul => "×"
  | Op.div => "÷"

-- 式全体をフォーマット
def formatExpression (op : Op) (a b : Int) : String :=
  let result := calculate op a b
  match result with
  | some n => s!"{a} {opSymbol op} {b} = {n}"
  | none   => s!"{a} {opSymbol op} {b} = エラー"

#eval formatExpression Op.add 10 3   -- "10 + 3 = 13"
#eval formatExpression Op.sub 10 3   -- "10 - 3 = 7"
#eval formatExpression Op.mul 10 3   -- "10 × 3 = 30"
#eval formatExpression Op.div 10 3   -- "10 ÷ 3 = 3"
#eval formatExpression Op.div 10 0   -- "10 ÷ 0 = エラー"

-- ============================================
-- 13. 応用: 式の木（Expression Tree）
-- ============================================
-- パターンマッチの真の力は「再帰的な型」に対して使うときに発揮される。
-- 数式を木構造で表現し、パターンマッチで評価する。

-- 算術式を表す型
inductive Expr where
  | lit (n : Int)              -- リテラル（数値そのもの）
  | add (e1 e2 : Expr)        -- 加算
  | mul (e1 e2 : Expr)        -- 乗算
  | neg (e : Expr)             -- 符号反転
  deriving Repr

-- 式を評価する（パターンマッチ + 再帰）
def evalExpr : Expr → Int
  | Expr.lit n      => n
  | Expr.add e1 e2  => evalExpr e1 + evalExpr e2
  | Expr.mul e1 e2  => evalExpr e1 * evalExpr e2
  | Expr.neg e      => - evalExpr e

-- (3 + 4) * 2 を表現
def expr1 := Expr.mul (Expr.add (Expr.lit 3) (Expr.lit 4)) (Expr.lit 2)
#eval evalExpr expr1  -- 14

-- -(5 + 3) を表現
def expr2 := Expr.neg (Expr.add (Expr.lit 5) (Expr.lit 3))
#eval evalExpr expr2  -- -8

-- 式を文字列に変換（pretty print）
def exprToString : Expr → String
  | Expr.lit n      => toString n
  | Expr.add e1 e2  => s!"({exprToString e1} + {exprToString e2})"
  | Expr.mul e1 e2  => s!"({exprToString e1} * {exprToString e2})"
  | Expr.neg e      => s!"(-{exprToString e})"

#eval exprToString expr1  -- "((3 + 4) * 2)"
#eval exprToString expr2  -- "(-(5 + 3))"

-- ============================================
-- 14. let パターンと関数引数でのパターンマッチ
-- ============================================
-- match 式だけでなく、let 束縛や関数引数でもパターンマッチできる。

-- let でタプルを分解
def addPair (pair : Nat × Nat) : Nat :=
  let (a, b) := pair  -- let パターン
  a + b

#eval addPair (3, 7)  -- 10

-- 関数引数で直接パターンマッチ（match不要）
def addPair' : Nat × Nat → Nat
  | (a, b) => a + b

#eval addPair' (3, 7)  -- 10

-- 複数引数でのパターンマッチ
def zipDescription : Nat → Nat → String
  | 0, 0 => "両方ゼロ"
  | 0, _ => "左がゼロ"
  | _, 0 => "右がゼロ"
  | n, m => s!"{n}と{m}"

#eval zipDescription 0 0  -- "両方ゼロ"
#eval zipDescription 0 5  -- "左がゼロ"
#eval zipDescription 3 0  -- "右がゼロ"
#eval zipDescription 3 5  -- "3と5"

-- ============================================
-- まとめ
-- ============================================
-- パターンマッチは Lean 4 プログラミングの根幹:
--
-- 1. match 式: 基本的なパターンマッチ
-- 2. Nat のマッチ: 0 と n+1 で自然数を分解
-- 3. Bool のマッチ: true/false を場合分け
-- 4. タプル: (a, b) で要素を取り出す
-- 5. ネスト: パターンの中にパターンを書ける
-- 6. ワイルドカード _: 使わない値を無視
-- 7. 複数パターン |: 同じ結果のケースをまとめる
-- 8. ガード: if と組み合わせて条件を追加
-- 9. 網羅性: コンパイラが全ケースを強制 → バグ防止
-- 10. 関数引数でもパターンマッチ可能
--
-- パターンマッチは「データの構造に沿って処理を書く」手法。
-- if-else の連鎖より意図が明確で、コンパイラの助けも得られる。
-- Lean で何かを書くとき、まず「この型のコンストラクタは何か？」を
-- 考えるクセをつけると、自然とパターンマッチが使えるようになる。

end Tutorial03
