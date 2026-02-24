# Lean 4 文法リファレンス

## 目次

1. [基本コマンド](#基本コマンド)
2. [型一覧](#型一覧)
3. [変数・定義](#変数定義)
4. [演算子](#演算子)
5. [関数](#関数)
6. [パターンマッチ](#パターンマッチ)
7. [リスト操作](#リスト操作)
8. [構造体 (structure)](#構造体-structure)
9. [帰納型 (inductive)](#帰納型-inductive)
10. [型クラス (class / instance)](#型クラス-class--instance)
11. [IO と do 記法](#io-と-do-記法)
12. [証明 (theorem / tactic)](#証明-theorem--tactic)
13. [依存型](#依存型)
14. [特殊構文・記号一覧](#特殊構文記号一覧)

---

## 基本コマンド

```lean
#eval 1 + 2          -- 式を評価して結果を表示
#check 1 + 2         -- 式の型を表示（Nat）
#check Nat            -- 型の型を表示（Type）
#print Nat            -- 定義を表示
```

---

## 型一覧

| 型 | 例 | 特徴 |
|---|---|---|
| `Nat` | `0`, `42`, `2^64` | 自然数。負なし。引き算は0で飽和（`3 - 10 = 0`）。0除算は0 |
| `Int` | `-5`, `0`, `42` | 整数。型注釈が必要：`(42 : Int)` |
| `Float` | `3.14`, `-1.5` | IEEE 754 64bit浮動小数点 |
| `String` | `"hello"` | UTF-8文字列。結合は `++`（`+` ではない） |
| `Bool` | `true`, `false` | 論理値 |
| `Char` | `'A'`, `'é'` | 単一文字（シングルクォート） |
| `Unit` | `()` | 空の値。返り値なしの関数に使用 |
| `List α` | `[1, 2, 3]` | 連結リスト |
| `Array α` | `#[1, 2, 3]` | 配列（高速ランダムアクセス） |
| `Option α` | `some 42`, `none` | 値があるかもしれない型 |
| `α × β` | `(1, "a")` | タプル（直積型） |
| `Fin n` | `Fin 5` | 0以上n未満の自然数 |
| `Prop` | `True`, `1 = 1` | 命題の型 |

---

## 変数・定義

```lean
-- 定数定義（トップレベル）
def myName : String := "Lean"
def myAge := 42                    -- 型推論あり

-- ローカル変数（let束縛、不変）
let x := 10
let y : Nat := x + 5

-- 型注釈（曖昧な場合に必要）
let n : Int := 42                  -- Natではなく Int にする
(42 : Int)                         -- 式内での型注釈
```

---

## 演算子

### 算術演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `+` | 加算 | `3 + 4` → `7` |
| `-` | 減算 | `10 - 3` → `7`（Natは飽和：`3 - 10` → `0`） |
| `*` | 乗算 | `3 * 4` → `12` |
| `/` | 除算 | `10 / 3` → `3`（整数除算）、`0` で割ると `0` |
| `%` | 剰余 | `10 % 3` → `1` |
| `^` | 累乗 | `2 ^ 10` → `1024` |

### 比較演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `==` | 等しい（Bool返却） | `3 == 3` → `true` |
| `!=` | 等しくない | `3 != 4` → `true` |
| `<` | 小なり | `3 < 5` → `true` |
| `>` | 大なり | `5 > 3` → `true` |
| `<=` / `≤` | 以下 | `3 <= 5` → `true` |
| `>=` / `≥` | 以上 | `5 >= 3` → `true` |
| `=` | 等号（命題、Prop） | `n = m`（証明で使う） |
| `≠` | 不等号（命題） | `n ≠ m` は `¬(n = m)` |

> **注意**: `==` は `Bool` を返す（プログラム用）。`=` は `Prop` を返す（証明用）。

### 論理演算子（Bool）

| 演算子 | 意味 | 例 |
|---|---|---|
| `&&` | AND | `true && false` → `false` |
| `\|\|` | OR | `true \|\| false` → `true` |
| `!` | NOT | `!true` → `false` |

### 論理結合子（Prop / 証明用）

| 記号 | 意味 | 入力方法 |
|---|---|---|
| `∧` | AND（かつ） | `\and` |
| `∨` | OR（または） | `\or` |
| `¬` | NOT（否定） | `\not` / `\neg` |
| `→` | ならば（含意） | `\to` / `\r` |
| `↔` | 同値（iff） | `\iff` / `\lr` |
| `∀` | すべての（全称） | `\all` / `\forall` |
| `∃` | 存在する（存在） | `\ex` / `\exists` |

### 文字列演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `++` | 文字列結合 | `"hello" ++ " " ++ "world"` |
| `s!"..."` | 文字列補間 | `s!"x = {x}"` |

### リスト演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `::` | 先頭に追加（cons） | `1 :: [2, 3]` → `[1, 2, 3]` |
| `++` | リスト結合 | `[1, 2] ++ [3, 4]` → `[1, 2, 3, 4]` |
| `[i]?` | インデックスアクセス（Option） | `[10, 20][1]?` → `some 20` |

### 関数演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `\|>` | パイプ（左→右） | `x \|> f \|> g`（`g (f x)`） |
| `<\|` | パイプ（右→左） | `f <\| g <\| x`（`f (g x)`） |
| `∘` | 関数合成（`\comp`） | `(f ∘ g) x` = `f (g x)` |
| `·` | プレースホルダー | `· * 2` は `fun x => x * 2` |
| `$` | 適用（括弧省略） | `f $ g x` は `f (g x)` |

### その他の演算子

| 演算子 | 意味 | 例 |
|---|---|---|
| `←` | doブロック内でIO実行 | `let x ← getLine` |
| `:=` | 定義・純粋値の束縛 | `let x := 42` |
| `⟨⟩` | 匿名コンストラクタ | `⟨3.0, 4.0⟩`（`\<` `\>`） |
| `▸` | 書き換え | 証明中の等式書き換え（`\t`） |

---

## 関数

### 基本定義

```lean
-- 名前付き関数
def add (x : Nat) (y : Nat) : Nat := x + y

-- 複数引数は自動的にカリー化される
-- add : Nat → Nat → Nat  =  Nat → (Nat → Nat)
```

### 無名関数（ラムダ）

```lean
fun x => x + 1                       -- 単一引数
fun (x : Nat) (y : Nat) => x + y     -- 型注釈付き
fun x y => x + y                     -- 省略形
```

### プレースホルダー記法

```lean
(· * 2)          -- fun x => x * 2
(· + ·)          -- fun x y => x + y
(· > 3)          -- fun x => x > 3
```

### 部分適用

```lean
def add (x y : Nat) : Nat := x + y
def add10 := add 10         -- add10 : Nat → Nat
#eval add10 5                -- 15
```

### where 句

```lean
def factorial (n : Nat) : Nat :=
  go n 1
  where
    go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc => go n ((n + 1) * acc)
```

### デフォルト引数 / 名前付き引数

```lean
def greet (name : String) (greeting : String := "Hello") : String :=
  s!"{greeting}, {name}!"

#eval greet "Alice"                    -- "Hello, Alice!"
#eval greet "Alice" "Hi"               -- "Hi, Alice!"
#eval greet (greeting := "Hey") (name := "Bob")  -- 名前付き引数
```

### 暗黙引数

```lean
-- {} で囲むと暗黙引数（呼び出し時に省略、推論される）
def listLength {α : Type} (xs : List α) : Nat := xs.length

-- 自動束縛：型変数 α は自動的に暗黙引数になる
def listLength (xs : List α) : Nat := xs.length  -- 同等
```

### 再帰関数と停止性

```lean
-- Lean は全関数を要求する（再帰が停止することの証明が必要）
-- n + 1 パターンで停止性を証明
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 停止性が証明できない場合は partial を使う
partial def collatz : Nat → Nat
  | 1 => 0
  | n => if n % 2 == 0 then 1 + collatz (n / 2)
         else 1 + collatz (3 * n + 1)
```

### 高階関数

```lean
-- 関数を引数に取る関数
def applyTwice (f : α → α) (x : α) : α := f (f x)
#eval applyTwice (· + 1) 10    -- 12

-- 主要な高階関数
List.map     : (α → β) → List α → List β
List.filter  : (α → Bool) → List α → List α
List.foldl   : (β → α → β) → β → List α → β
List.foldr   : (α → β → β) → β → List α → β
```

---

## パターンマッチ

### match 式

```lean
match value with
| pattern1 => result1
| pattern2 => result2
| _        => default     -- ワイルドカード（何にでもマッチ）
```

### パターンの種類

```lean
-- リテラル
| 0 => ...
| "hello" => ...
| true => ...

-- 変数束縛
| n => ...                -- 任意の値を n に束縛

-- コンストラクタ
| some x => ...
| none => ...
| .circle r => ...        -- ドット記法（型が推論可能な場合）

-- Nat の後続（succ）パターン
| 0 => ...
| n + 1 => ...            -- n は n-1 の値

-- タプル
| (a, b) => ...
| (0, _) => ...

-- リスト
| [] => ...               -- 空リスト
| [x] => ...              -- 要素1つ
| [x, y] => ...           -- 要素2つ
| x :: xs => ...          -- head :: tail
| x :: y :: rest => ...   -- 先頭2要素 + 残り

-- ネスト
| some (some n) => ...
| (0, x :: _) => ...

-- 選択肢（|）
| 'a' | 'e' | 'i' | 'o' | 'u' => "vowel"
```

### 関数引数での直接パターンマッチ

```lean
-- match なしで直接パターンマッチ
def isZero : Nat → Bool
  | 0 => true
  | _ => false

-- 複数引数
def describe : Nat → Nat → String
  | 0, 0 => "both zero"
  | 0, _ => "left zero"
  | _, 0 => "right zero"
  | n, m => s!"{n} and {m}"
```

### 網羅性チェック

Lean はすべてのケースをカバーすることを**コンパイル時に要求**する。
不足するパターンがあるとエラーになる。

---

## リスト操作

### 生成

```lean
[1, 2, 3]                    -- リテラル
1 :: 2 :: 3 :: []             -- cons で構築
List.range 5                  -- [0, 1, 2, 3, 4]
List.replicate 3 "x"          -- ["x", "x", "x"]
([] : List Nat)               -- 空リスト（型注釈が必要）
```

### 基本操作

```lean
xs.length                     -- 長さ
xs.reverse                    -- 逆順
xs ++ ys                      -- 結合
xs.head?                      -- 先頭（Option）
xs.tail?                      -- 先頭以外（Option）
xs.getLast?                   -- 末尾（Option）
xs[2]?                        -- インデックスアクセス（Option、0始まり）
xs.isEmpty                    -- 空かどうか
xs.contains x                 -- 要素が含まれるか
xs.take n                     -- 先頭 n 個
xs.drop n                     -- 先頭 n 個をスキップ
xs.zip ys                     -- ペアにする：[(x1,y1), (x2,y2), ...]
xs.eraseDups                  -- 重複除去
```

### 変換・フィルタ

```lean
xs.map (· * 2)                -- 各要素を変換
xs.filter (· > 3)             -- 条件を満たす要素のみ
xs.filterMap f                -- map + filter（none を除外）
xs.flatMap f                  -- map して flatten
xs.find? (· > 3)              -- 最初にマッチする要素（Option）
xs.any (· > 3)                -- いずれかが条件を満たすか
xs.all (· > 0)                -- すべてが条件を満たすか
```

### 畳み込み（fold）

```lean
-- foldl : 左から畳み込み
[1, 2, 3, 4].foldl (· + ·) 0   -- ((((0+1)+2)+3)+4) = 10

-- foldr : 右から畳み込み
[1, 2, 3].foldr (· :: ·) []     -- 1 :: (2 :: (3 :: [])) = [1,2,3]
```

### パイプでチェーン

```lean
xs.map (fun x => x * x)
  |>.filter (· % 2 == 0)
  |>.foldl (· + ·) 0
```

### Option の扱い

```lean
some 42                       -- 値あり
none                          -- 値なし
opt.getD 0                    -- デフォルト値付き取得
opt.map (· * 2)               -- some なら変換、none ならそのまま
opt.bind f                    -- some なら f を適用（f も Option を返す）
```

---

## 構造体 (structure)

### 定義

```lean
structure Point where
  x : Float
  y : Float
  deriving Repr         -- #eval で表示可能にする
```

### インスタンス生成

```lean
-- 方法1: 名前付き構文
def p1 : Point := { x := 3.0, y := 4.0 }

-- 方法2: コンストラクタ
def p2 : Point := Point.mk 3.0 4.0

-- 方法3: 匿名コンストラクタ
def p3 : Point := ⟨3.0, 4.0⟩
```

### フィールドアクセス・更新

```lean
p1.x                                 -- フィールドアクセス
{ p1 with x := 10.0 }                -- 不変更新（新しいインスタンスを生成）
```

### メソッド（名前空間内の関数）

```lean
def Point.distance (p : Point) : Float :=
  (p.x * p.x + p.y * p.y).sqrt

-- ドット記法で呼び出し可能
#eval p1.distance
```

### デフォルト値

```lean
structure Config where
  host : String := "localhost"
  port : Nat := 8080
  debug : Bool := false

def cfg : Config := {}                   -- すべてデフォルト
def dev : Config := { debug := true }    -- 一部だけ指定
```

### ジェネリック構造体

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr
```

### namespace でメソッドをまとめる

```lean
namespace Point
  def translate (p : Point) (dx dy : Float) : Point :=
    { p with x := p.x + dx, y := p.y + dy }
  def scale (p : Point) (factor : Float) : Point :=
    ⟨p.x * factor, p.y * factor⟩
end Point
```

---

## 帰納型 (inductive)

### 列挙型

```lean
inductive Direction where
  | north | south | east | west
  deriving Repr, BEq
```

### データを持つコンストラクタ

```lean
inductive Shape where
  | circle (radius : Float)
  | rectangle (width : Float) (height : Float)
  | triangle (base : Float) (height : Float)
  deriving Repr
```

### パターンマッチで処理

```lean
def Shape.area : Shape → Float
  | .circle r => 3.14159 * r * r
  | .rectangle w h => w * h
  | .triangle b h => 0.5 * b * h
```

### ジェネリック帰納型

```lean
-- Option（自作版）
inductive MyOption (α : Type) where
  | none : MyOption α
  | some : α → MyOption α

-- Result / Either
inductive Result (ε α : Type) where
  | ok : α → Result ε α
  | err : ε → Result ε α
```

### 再帰的帰納型

```lean
-- 二分木
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

-- 式木
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
```

### JSON風の相互再帰

```lean
inductive JsonValue where
  | null
  | bool : Bool → JsonValue
  | num : Float → JsonValue
  | str : String → JsonValue
  | array : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue
```

---

## 型クラス (class / instance)

### 定義

```lean
class Greetable (α : Type) where
  greet : α → String
```

### インスタンス実装

```lean
instance : Greetable String where
  greet s := s!"Hello, {s}!"
```

### 主要な組み込み型クラス

| 型クラス | 用途 | 提供する機能 |
|---|---|---|
| `ToString` | 文字列変換 | `toString x` |
| `Repr` | デバッグ表示 | `#eval` で表示 |
| `BEq` | 等価比較 | `==`, `!=` |
| `Ord` | 順序比較 | `compare a b` → `.lt` / `.eq` / `.gt` |
| `Inhabited` | デフォルト値 | `default` |
| `Add` | 加算 | `+` |
| `Mul` | 乗算 | `*` |
| `HAdd` | 異なる型の加算 | 型が異なる `+` |

### deriving で自動導出

```lean
structure Point where
  x : Float
  y : Float
  deriving Repr, BEq, Inhabited

inductive Color where
  | red | green | blue
  deriving Repr, BEq, Inhabited
```

### 型クラス制約付きジェネリック関数

```lean
-- [制約名 型変数] で指定
def maxOf [Ord α] (a b : α) : α :=
  if compare a b == .gt then a else b

def showEqual [BEq α] [ToString α] (a b : α) : String :=
  if a == b then s!"{a} == {b}" else s!"{a} != {b}"

-- 複数制約
def sortAndShow [Ord α] [ToString α] (xs : List α) : String := ...
```

---

## IO と do 記法

### 基本 IO

```lean
IO.println "Hello"            -- 改行あり出力
IO.print "Hello"              -- 改行なし出力
IO.eprintln "Error!"          -- 標準エラー出力
```

### do ブロック

```lean
def main : IO Unit := do
  IO.println "Line 1"
  IO.println "Line 2"
```

### let 束縛（do 内）

```lean
do
  let x := 42                -- 純粋値の束縛（:=）
  let line ← IO.getStdin >>= (·.getLine)  -- IO値の束縛（←）
  IO.println s!"got: {line}"
```

> **`:=`** は純粋な値、**`←`** は IO アクションの結果を取り出す。

### 可変変数

```lean
do
  let mut counter := 0
  counter := counter + 1      -- 再代入可能
  counter := counter + 1
  IO.println s!"{counter}"    -- 2
```

### for ループ

```lean
do
  for item in [1, 2, 3] do
    IO.println s!"{item}"

  for i in List.range 10 do   -- 0..9
    IO.println s!"i = {i}"
```

### while / repeat

```lean
do
  let mut n := 0
  while n < 5 do
    n := n + 1

  let mut m := 0
  repeat
    if m >= 5 then break
    m := m + 1
```

### 返り値

```lean
def compute : IO Nat := do
  return 42                   -- return で値を返す

def compute2 : IO Nat := do
  pure 42                     -- pure でも同じ
```

### 早期 return

```lean
def findFirst (xs : List Nat) : IO (Option Nat) := do
  for x in xs do
    if x > 10 then return some x
  return none
```

### エラーハンドリング

```lean
do
  try
    let result ← riskyAction
    IO.println s!"{result}"
  catch e =>
    IO.println s!"Error: {e}"
  finally
    IO.println "Cleanup"

-- エラーを投げる
throw (IO.Error.userError "Something went wrong")
```

### ユーザー入力

```lean
do
  IO.print "Name: "
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let name := input.trim
  IO.println s!"Hello, {name}!"
```

### main 関数

```lean
-- 基本形
def main : IO Unit := do
  IO.println "Hello, World!"

-- コマンドライン引数付き
def main (args : List String) : IO Unit := do
  for arg in args do
    IO.println arg

-- 終了コード付き
def main : IO UInt32 := do
  return 0   -- 成功
```

---

## 証明 (theorem / tactic)

### 基本構文

```lean
-- 項モード（直接証明の値を構築）
theorem name : proposition := proof_term

-- タクティクモード（by の後にタクティクを列挙）
theorem name : proposition := by
  tactic1
  tactic2
```

### 主要タクティク一覧

| タクティク | 用途 | 例 |
|---|---|---|
| `intro h` | 仮定を導入 | `P → Q` の `P` を仮定 `h` として導入 |
| `exact term` | 完全一致する項で証明 | ゴールと型が一致する項を提供 |
| `apply f` | 関数を逆方向に適用 | ゴールが `Q` で `f : P → Q` なら、ゴールは `P` に変化 |
| `rfl` | 反射律（`x = x`） | `2 + 3 = 5` など計算で等しいものも |
| `constructor` | コンストラクタで分解 | `P ∧ Q` を2つのゴールに分割 |
| `cases h` | 場合分け | `P ∨ Q` を `P` の場合と `Q` の場合に分割 |
| `induction n` | 帰納法 | `zero` と `succ` のケースに分割 |
| `have h : T := proof` | 中間補題 | 証明中で補助的な命題を示す |
| `assumption` | 仮定からゴールに一致するものを使用 | |
| `simp` | 単純化 | 自動的に式を簡約 |
| `simp [h]` | 仮定/補題を使って単純化 | |
| `omega` | 線形算術を自動証明 | `n + m = m + n` など |
| `decide` | 決定可能な命題を計算で証明 | `2 + 3 = 5` など具体的な値 |
| `left` | 左の選言を選択 | ゴール `P ∨ Q` → ゴール `P` |
| `right` | 右の選言を選択 | ゴール `P ∨ Q` → ゴール `Q` |
| `absurd hp hnp` | 矛盾から証明 | `hp : P` と `hnp : ¬P` から任意の命題 |
| `split` | if/match を場合分け | 条件分岐のある定義の証明 |
| `unfold name` | 定義を展開 | |
| `rw [h]` | 等式で書き換え | `h : a = b` でゴール中の `a` を `b` に |

### フォーカス記法

```lean
-- · でサブゴールにフォーカス
theorem example : P ∧ Q := by
  constructor
  · exact hp      -- 1つ目のゴール
  · exact hq      -- 2つ目のゴール

-- <;> で全サブゴールに同じタクティク
constructor <;> assumption
```

### 証明の例

```lean
-- 等式
theorem one_plus_one : 1 + 1 = 2 := by rfl

-- 論理積の交換
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

-- 論理和の交換
theorem or_comm (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

-- 対偶
theorem contrapositive (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq hp
  exact hnq (hpq hp)

-- ド・モルガン
theorem de_morgan (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  · intro hp; exact h (Or.inl hp)
  · intro hq; exact h (Or.inr hq)

-- 自然数の算術
theorem add_comm_nat (n m : Nat) : n + m = m + n := by omega
```

### Prop の基本値

```lean
True.intro         -- True の証明
False.elim h       -- False から任意の命題を証明（爆発律）
And.intro hp hq    -- P ∧ Q の証明（⟨hp, hq⟩ とも書ける）
Or.inl hp          -- P ∨ Q の証明（左）
Or.inr hq          -- P ∨ Q の証明（右）
h.left / h.1       -- P ∧ Q から P を取得
h.right / h.2      -- P ∧ Q から Q を取得
h.mp               -- (P ↔ Q) から P → Q
h.mpr              -- (P ↔ Q) から Q → P
```

---

## 依存型

### Fin n（有界自然数）

```lean
-- 0 ≤ val < n を保証する型
def x : Fin 5 := ⟨3, by omega⟩   -- 3 < 5 の証明付き
def y : Fin 5 := 2                -- リテラルは自動チェック

-- 安全な配列アクセス
#eval #["a", "b", "c"][1]         -- "b"（範囲外はコンパイルエラー）
```

### Vect（長さ付きリスト）

```lean
-- 型レベルで長さを持つリスト
inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- 空リストに head は呼べない（型エラー）
def Vect.head : Vect α (n + 1) → α
  | .cons x _ => x
```

### Subtype（述語付き型）

```lean
-- { x : α // P x } = P を満たす α の値
abbrev PositiveNat := { n : Nat // n > 0 }

def three : PositiveNat := ⟨3, by omega⟩
-- ⟨0, by omega⟩ はエラー（0 > 0 は偽）

-- 安全な除算
def safeDiv (a : Nat) (b : PositiveNat) : Nat :=
  a / b.val
```

### 型レベル状態マシン

```lean
-- ドアの状態を型で表現
inductive DoorState where | opened | closed
inductive Door : DoorState → Type where
  | mk : String → Door s

-- 閉じたドアだけ開けられる（型で保証）
def openDoor : Door .closed → Door .opened
  | Door.mk label => Door.mk label

-- 開いたドアを開こうとすると型エラー
```

---

## 特殊構文・記号一覧

### キーワード

| キーワード | 用途 |
|---|---|
| `def` | 関数/値の定義 |
| `let` | ローカル変数束縛（不変） |
| `let mut` | ローカル変数束縛（可変、do内のみ） |
| `where` | ローカル定義 |
| `if`/`then`/`else` | 条件分岐 |
| `match`/`with` | パターンマッチ |
| `fun`/`=>` | 無名関数 |
| `do` | 手続き的ブロック |
| `for`/`in` | ループ |
| `while` | 条件ループ |
| `repeat`/`break` | 無限ループ + 脱出 |
| `return` | 値を返す（do内） |
| `pure` | 値をモナドに持ち上げ |
| `try`/`catch`/`finally` | エラーハンドリング |
| `throw` | エラーを投げる |
| `structure` | 構造体定義 |
| `inductive` | 帰納型定義 |
| `class` | 型クラス定義 |
| `instance` | 型クラスインスタンス |
| `namespace`/`end` | 名前空間 |
| `open` | 名前空間を開く |
| `theorem` | 定理（証明） |
| `example` | 無名の定理 |
| `by` | タクティクモード開始 |
| `deriving` | 型クラスの自動導出 |
| `partial` | 停止性証明をスキップ |
| `private` | 外部から非公開 |
| `protected` | 完全修飾名が必要 |
| `abbrev` | 透過的な型エイリアス |
| `section`/`end` | セクション |
| `variable` | 暗黙の引数宣言 |
| `import` | モジュールのインポート |
| `#eval` | 式の評価 |
| `#check` | 型の確認 |
| `#print` | 定義の表示 |

### Unicode 記号の入力方法（VS Code）

| 記号 | 入力 | 意味 |
|---|---|---|
| `→` | `\to` or `\r` | 関数の型 / 含意 |
| `←` | `\l` | do内のIO束縛 |
| `↔` | `\iff` or `\lr` | 同値 |
| `∧` | `\and` | 論理積 |
| `∨` | `\or` | 論理和 |
| `¬` | `\not` or `\neg` | 否定 |
| `∀` | `\all` or `\forall` | 全称量化 |
| `∃` | `\ex` or `\exists` | 存在量化 |
| `α` | `\a` | 型変数によく使う |
| `β` | `\b` | 型変数 |
| `γ` | `\g` | 型変数 |
| `ε` | `\e` | エラー型によく使う |
| `∘` | `\comp` | 関数合成 |
| `×` | `\x` or `\times` | 直積型 |
| `⟨⟩` | `\<` `\>` | 匿名コンストラクタ |
| `≤` | `\le` | 以下 |
| `≥` | `\ge` | 以上 |
| `≠` | `\ne` | 不等号 |
| `▸` | `\t` | 書き換え |
| `⟩` | `\>` | 閉じ山括弧 |
| `·` | `\.` | プレースホルダー |
| `λ` | `\lam` | ラムダ（funの別表記） |

### よくあるパターン集

```lean
-- Option の安全な取り出し
match result with
| some x => s!"Got {x}"
| none => "Nothing"

-- リストの再帰処理
def process : List α → Result
  | [] => base_case
  | x :: xs => combine x (process xs)

-- パイプで変換チェーン
data |>.map transform |>.filter predicate |>.foldl combine init

-- if-let パターン（Lean 4.x）
if let some x := optionalValue then
  use x
else
  handleNone

-- do 記法での典型パターン
def main : IO Unit := do
  let input ← readInput
  let result := processData input
  IO.println s!"{result}"
```
