-- ============================================
-- Tutorial 04: Lean 4 のリスト (List) 完全ガイド
-- 他言語経験者向け / Japanese comments
-- ============================================
-- このファイルは単体でコンパイルできます。
-- #eval の結果はエディタ上(VS Code + lean4 拡張)でホバーすると確認できます。

namespace Tutorial04

-- ============================================
-- 1. リストリテラルと型注釈
-- ============================================
-- Lean のリストは Python の list や Haskell の [a] に近い。
-- ただし全要素が同じ型でなければならない（TypeScript の number[] と同じ感覚）。

-- 基本的なリストリテラル
#eval [1, 2, 3]           -- [1, 2, 3]   型は List Nat と推論される
#eval ["hello", "world"]  -- ["hello", "world"]   型は List String

-- 型注釈を明示する書き方
-- 他言語でいう let xs: number[] = [1,2,3] のようなもの
def xs : List Nat := [1, 2, 3]
def ys : List String := ["a", "b", "c"]

#eval xs  -- [1, 2, 3]
#eval ys  -- ["a", "b", "c"]

-- 空リストには型注釈が必要（型推論できないため）
def emptyNats : List Nat := []
#eval emptyNats  -- []

-- (List Nat) と書く代わりに、配列風に書くこともできる
-- ただし Lean では List が基本。Array は別の型。
#eval ([] : List Nat)  -- 空リストに型をつけるもう一つの方法

-- ============================================
-- 2. Cons 演算子 (::) --- リストの基本構造
-- ============================================
-- Lean の List は「先頭要素 :: 残りのリスト」という再帰構造。
-- これは Haskell の (:) と同じ。JavaScript にはない概念。
--
-- 内部的には:
--   List.nil          = []
--   List.cons 1 []    = [1]
--   List.cons 1 (List.cons 2 []) = [1, 2]
--
-- :: は List.cons の糖衣構文（シンタックスシュガー）。

#eval 0 :: [1, 2, 3]      -- [0, 1, 2, 3]   先頭に追加（O(1)）
#eval 1 :: 2 :: 3 :: []   -- [1, 2, 3]       これがリストの正体
#eval 42 :: []             -- [42]            要素1つのリスト

-- :: は右結合なので、1 :: 2 :: 3 :: [] は 1 :: (2 :: (3 :: [])) と同じ
-- つまり「右から順に組み立てる」イメージ

-- 変数でも使える
def myList := 10 :: 20 :: 30 :: []
#eval myList  -- [10, 20, 30]

-- ============================================
-- 3. 基本操作: length, reverse, append (++)
-- ============================================

-- List.length --- リストの長さ
#eval [1, 2, 3].length        -- 3
#eval ([] : List Nat).length  -- 0
#eval List.length [10, 20]    -- 2   メソッド構文でも関数構文でもOK

-- List.reverse --- リストの反転
#eval [1, 2, 3].reverse   -- [3, 2, 1]
#eval ["a", "b"].reverse   -- ["b", "a"]

-- List.append (++) --- リストの連結
-- 他言語の concat や + に相当
#eval [1, 2] ++ [3, 4]          -- [1, 2, 3, 4]
#eval [1, 2].append [3, 4]      -- [1, 2, 3, 4]   同じこと
#eval [] ++ [1, 2, 3]           -- [1, 2, 3]
#eval [1] ++ [2] ++ [3]         -- [1, 2, 3]

-- ++ は先頭側のリストを走査するので、左が短い方が効率的
-- 計算量: O(左リストの長さ)

-- ============================================
-- 4. map, filter, foldl, foldr --- 関数型の三種の神器
-- ============================================

-- ■ List.map --- 各要素に関数を適用（JS の .map() と同じ）
#eval [1, 2, 3].map (fun x => x * 2)      -- [2, 4, 6]
#eval [1, 2, 3].map (· * 2)               -- [2, 4, 6]   · は無名引数の省略記法
#eval [1, 2, 3].map (· + 10)              -- [11, 12, 13]
#eval ["hello", "world"].map String.length -- [5, 5]
#eval [1, 2, 3].map toString               -- ["1", "2", "3"]

-- map の型: List.map : (α → β) → List α → List β
-- 入力リストの型と出力リストの型は違ってもよい

-- ■ List.filter --- 条件を満たす要素だけ残す（JS の .filter() と同じ）
#eval [1, 2, 3, 4, 5].filter (fun x => x > 3)   -- [4, 5]
#eval [1, 2, 3, 4, 5].filter (· > 3)             -- [4, 5]   省略記法
#eval [1, 2, 3, 4, 5, 6].filter (fun x => x % 2 == 0)  -- [2, 4, 6]   偶数だけ

-- filter の述語は Bool を返す関数（Lean では BEq や Ord が必要な場面もある）
#eval ["apple", "banana", "avocado"].filter (fun s => s.startsWith "a")
-- ["apple", "avocado"]

-- ■ List.foldl --- 左から畳み込み（JS の .reduce() に相当）
-- foldl (fun acc x => ...) init xs
-- init から始めて、左から順に accumulator に要素を食わせていく
#eval [1, 2, 3, 4].foldl (· + ·) 0     -- 10   (((0+1)+2)+3)+4
#eval [1, 2, 3, 4].foldl (· * ·) 1     -- 24   (((1*1)*2)*3)*4
#eval ["a", "b", "c"].foldl (· ++ ·) "" -- "abc"

-- 累積の順序を見てみよう
-- foldl f init [x1, x2, x3] = f (f (f init x1) x2) x3
-- つまり「左から順に処理」

-- ■ List.foldr --- 右から畳み込み
-- foldr (fun x acc => ...) init xs
-- 右端から処理していく（Haskell の foldr と同じ）
#eval [1, 2, 3].foldr (· + ·) 0    -- 6    1+(2+(3+0))
#eval [1, 2, 3].foldr (· :: ·) []  -- [1, 2, 3]   リストのコピー！

-- foldr f init [x1, x2, x3] = f x1 (f x2 (f x3 init))
-- cons (::) で foldr すると元のリストが復元される。これがリストの本質。

-- foldl vs foldr:
--   foldl は末尾再帰で効率的（大きなリストに向く）
--   foldr はリスト構造を保つ操作に自然

-- ============================================
-- 5. 安全なアクセス: head?, tail?, xs[i]? と Option 型
-- ============================================
-- Lean は「安全性」を重視する言語。
-- 空リストの先頭要素を取ろうとすると、例外ではなく Option 型が返る。
-- Option は Rust の Option / TypeScript の T | undefined に相当。

-- Option 型のおさらい:
--   some x  = 値がある（Rust の Some(x)）
--   none    = 値がない（Rust の None）

-- ■ List.head? --- 先頭要素を安全に取得
#eval [1, 2, 3].head?          -- some 1
#eval ([] : List Nat).head?    -- none
#eval ["hello"].head?          -- some "hello"

-- ■ List.tail? --- 先頭以外を安全に取得
#eval [1, 2, 3].tail?          -- some [2, 3]
#eval [1].tail?                -- some []
#eval ([] : List Nat).tail?    -- none

-- ■ xs[i]? --- インデックスで安全にアクセス（0始まり）
-- 他言語の xs[i] に相当するが、範囲外は none を返す（例外は飛ばない）
#eval [10, 20, 30][0]?   -- some 10
#eval [10, 20, 30][1]?   -- some 20
#eval [10, 20, 30][2]?   -- some 30
#eval [10, 20, 30][3]?   -- none     範囲外！でも安全

-- ■ List.getLast? --- 末尾要素を安全に取得
#eval [1, 2, 3].getLast?        -- some 3
#eval ([] : List Nat).getLast?  -- none

-- ============================================
-- 6. Option 型をもう少し深く
-- ============================================
-- Option は Lean では超頻出。リスト操作に限らず至るところで使われる。

-- Option の定義（参考）:
-- inductive Option (α : Type) where
--   | none : Option α
--   | some : α → Option α

-- Option から値を取り出す方法いろいろ

-- 方法1: Option.getD --- デフォルト値付きで取り出す（Rust の unwrap_or）
#eval [1, 2, 3].head?.getD 0        -- 1     値がある場合
#eval ([] : List Nat).head?.getD 0   -- 0     none の場合はデフォルト値

-- 方法2: パターンマッチ
def showHead (xs : List Nat) : String :=
  match xs.head? with
  | some x => s!"先頭は {x}"    -- s!"..." は文字列補間（JS のテンプレートリテラル風）
  | none   => "リストが空です"

#eval showHead [42, 99]   -- "先頭は 42"
#eval showHead []          -- "リストが空です"

-- 方法3: Option.map --- Option の中身に関数を適用
#eval (some 5).map (· * 2)       -- some 10
#eval (none : Option Nat).map (· * 2)  -- none
#eval [1, 2, 3].head?.map toString     -- some "1"

-- 方法4: Option.bind --- Option を返す関数をチェーン（flatMap 的な）
#eval (some [1, 2, 3]).bind List.head?  -- some 1
#eval (some ([] : List Nat)).bind List.head?  -- none
#eval (none : Option (List Nat)).bind List.head?  -- none

-- ============================================
-- 7. zip と enumerate
-- ============================================

-- ■ List.zip --- 2つのリストをペアにする（Python の zip と同じ）
#eval [1, 2, 3].zip ["a", "b", "c"]        -- [(1, "a"), (2, "b"), (3, "c")]
#eval [1, 2].zip ["a", "b", "c"]           -- [(1, "a"), (2, "b")]   短い方に合わせる
#eval [1, 2, 3].zip [10, 20, 30]           -- [(1, 10), (2, 20), (3, 30)]

-- zip の結果はタプル (Prod 型) のリスト
-- タプルは (a, b) で作り、.1 .2 でアクセスする
#eval (1, "hello").1    -- 1
#eval (1, "hello").2    -- "hello"

-- zipWith --- zip + map を同時にやる
-- List.zipWith f xs ys = (xs.zip ys).map (fun (a,b) => f a b)
#eval List.zipWith (· + ·) [1, 2, 3] [10, 20, 30]   -- [11, 22, 33]
#eval List.zipWith (· * ·) [2, 3, 4] [10, 10, 10]    -- [20, 30, 40]

-- ■ インデックス付きにする（Python の enumerate と同じ）
-- Lean 4.28 では List.enum が無いので zip + range で実現
def myEnum (xs : List α) : List (Nat × α) :=
  (List.range xs.length).zip xs

#eval myEnum ["a", "b", "c"]     -- [(0, "a"), (1, "b"), (2, "c")]
#eval myEnum [10, 20, 30]        -- [(0, 10), (1, 20), (2, 30)]

-- myEnum + map でインデックス付き処理
#eval myEnum ["apple", "banana", "cherry"] |>.map
  (fun (i, s) => s!"{i}: {s}")
-- ["0: apple", "1: banana", "2: cherry"]

-- ============================================
-- 8. range と replicate --- リストの生成
-- ============================================

-- ■ List.range --- 0 から n-1 までのリストを生成
#eval List.range 5         -- [0, 1, 2, 3, 4]
#eval List.range 0         -- []
#eval List.range 10        -- [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

-- range + map で好きな数列を作る
#eval (List.range 5).map (· * 2)       -- [0, 2, 4, 6, 8]   偶数列
#eval (List.range 5).map (· + 1)       -- [1, 2, 3, 4, 5]   1始まり

-- ■ List.replicate --- 同じ値を n 個並べる
#eval List.replicate 3 "ha"    -- ["ha", "ha", "ha"]
#eval List.replicate 5 0       -- [0, 0, 0, 0, 0]
#eval List.replicate 0 42      -- []

-- ============================================
-- 9. パターンマッチとリスト --- 関数型プログラミングの真髄
-- ============================================
-- リストのパターンマッチは Lean/Haskell の最も強力な機能の一つ。
-- switch/case とは比較にならない表現力がある。

-- パターンの基本:
--   []       = 空リスト
--   h :: t   = 先頭(head) と残り(tail) に分解
--   [x]      = 要素1つのリスト（x :: [] の糖衣構文）
--   x :: y :: t = 先頭2つと残り

-- 例: リストの最初の要素を文字列で返す
def describeListV2 (xs : List Nat) : String :=
  match xs with
  | []     => "空リスト"
  | [x]    => s!"要素が1つ: {x}"
  | x :: _ => s!"先頭は {x} で、他にも要素がある"

#eval describeListV2 []          -- "空リスト"
#eval describeListV2 [42]        -- "要素が1つ: 42"
#eval describeListV2 [1, 2, 3]   -- "先頭は 1 で、他にも要素がある"

-- 先頭2つを取り出すパターンマッチ
def firstTwo (xs : List Nat) : String :=
  match xs with
  | x :: y :: _ => s!"最初の2つ: {x}, {y}"
  | [x]         => s!"1つだけ: {x}"
  | []          => "空"

#eval firstTwo [10, 20, 30]   -- "最初の2つ: 10, 20"
#eval firstTwo [10]           -- "1つだけ: 10"
#eval firstTwo []             -- "空"

-- ============================================
-- 10. 再帰関数とリスト
-- ============================================
-- Lean の List は再帰的データ構造なので、再帰関数と相性抜群。
-- for ループの代わりに再帰を使うのが関数型スタイル。

-- ■ 合計 (sum)
def mySum : List Nat -> Nat
  | []      => 0                -- 空リストの合計は 0（基底ケース）
  | h :: t  => h + mySum t      -- 先頭 + 残りの合計（再帰ケース）

#eval mySum [1, 2, 3, 4, 5]    -- 15
#eval mySum []                  -- 0
#eval mySum [100]               -- 100

-- ■ 積 (product)
def myProduct : List Nat -> Nat
  | []      => 1                -- 空リストの積は 1（単位元）
  | h :: t  => h * myProduct t

#eval myProduct [1, 2, 3, 4]   -- 24
#eval myProduct [10, 20]        -- 200
#eval myProduct []              -- 1

-- ■ 含まれるか判定 (contains)
-- BEq は == で比較可能な型を表す型クラス（他言語の interface/trait に相当）
def myContains [BEq α] (x : α) : List α -> Bool
  | []     => false
  | h :: t => h == x || myContains x t

#eval myContains 3 [1, 2, 3, 4]   -- true
#eval myContains 5 [1, 2, 3, 4]   -- false
#eval myContains "b" ["a", "b"]    -- true

-- ■ リストの各要素を2倍にする (doubleAll)
def doubleAll : List Nat -> List Nat
  | []     => []
  | h :: t => (h * 2) :: doubleAll t

#eval doubleAll [1, 2, 3]   -- [2, 4, 6]
-- もちろん .map (· * 2) で済むが、再帰の理解のために書いている

-- ■ 独自の filter を再帰で実装
def myFilter (p : α -> Bool) : List α -> List α
  | []     => []
  | h :: t => if p h then h :: myFilter p t else myFilter p t

#eval myFilter (· > 3) [1, 2, 3, 4, 5]   -- [4, 5]
#eval myFilter (· % 2 == 0) [1, 2, 3, 4, 5, 6]  -- [2, 4, 6]

-- ■ リストの最大値を求める
def myMax : List Nat -> Nat
  | []      => 0
  | [x]     => x
  | x :: xs => let m := myMax xs; if x > m then x else m

#eval myMax [3, 1, 4, 1, 5, 9, 2, 6]   -- 9
#eval myMax [42]                         -- 42
#eval myMax []                           -- 0

-- ■ リストの平坦化 (flatten / concat)
-- [[1,2],[3],[4,5]] → [1,2,3,4,5]
def myFlatten : List (List α) -> List α
  | []      => []
  | h :: t  => h ++ myFlatten t

#eval myFlatten [[1, 2], [3], [4, 5]]    -- [1, 2, 3, 4, 5]
#eval myFlatten [["a", "b"], ["c"]]       -- ["a", "b", "c"]
#eval myFlatten ([] : List (List Nat))    -- []

-- 標準ライブラリには List.flatten (旧名 List.join) がある
#eval [[1, 2], [3], [4, 5]].flatten    -- [1, 2, 3, 4, 5]

-- ============================================
-- 11. filterMap --- filter + map を一発で（リスト内包表記風）
-- ============================================
-- Python の [f(x) for x in xs if cond(x)] に近い操作。
-- filterMap は「Option を返す関数」を渡し、some なら値を採用、none なら除外。

-- 型: List.filterMap : (α → Option β) → List α → List β

-- 例: 偶数だけ2倍にして取り出す
#eval [1, 2, 3, 4, 5, 6].filterMap
  (fun x => if x % 2 == 0 then some (x * 2) else none)
-- [4, 8, 12]

-- 例: 文字列を数値に変換（変換できないものは除外）
#eval ["123", "abc", "456", ""].filterMap String.toNat?
-- [123, 456]
-- String.toNat? は String -> Option Nat で、数値に変換できなければ none を返す

-- 例: リストから3より大きい数だけ取り出して文字列にする
#eval [1, 2, 3, 4, 5, 6].filterMap
  (fun x => if x > 3 then some (toString x) else none)
-- ["4", "5", "6"]

-- filterMap は flatMap 的にも使える
-- none を除外する用途
#eval [some 1, none, some 3, none, some 5].filterMap id
-- [1, 3, 5]
-- id は恒等関数（そのまま返す）。Option α → Option α なので filterMap にぴったり。

-- ============================================
-- 12. その他の便利な関数
-- ============================================

-- ■ List.take / List.drop --- 先頭 n 個を取る / 先頭 n 個を捨てる
#eval [1, 2, 3, 4, 5].take 3      -- [1, 2, 3]
#eval [1, 2, 3, 4, 5].drop 3      -- [4, 5]
#eval [1, 2, 3].take 10           -- [1, 2, 3]   足りなくても安全

-- ■ List.any / List.all --- 条件を満たす要素があるか / 全て満たすか
#eval [1, 2, 3, 4].any (· > 3)     -- true    4 > 3 があるから
#eval [1, 2, 3, 4].all (· > 3)     -- false   1, 2, 3 は > 3 でない
#eval [4, 5, 6].all (· > 3)        -- true    全部 > 3

-- ■ List.find? --- 条件を満たす最初の要素を探す
#eval [1, 2, 3, 4, 5].find? (· > 3)     -- some 4
#eval [1, 2, 3].find? (· > 10)          -- none

-- ■ List.map + flatten = flatMap 的な操作
-- List.flatMap のように「各要素をリストにして平坦化」
#eval [1, 2, 3].flatMap (fun x => [x, x * 10])
-- [1, 10, 2, 20, 3, 30]

-- ■ List.isEmpty
#eval [1, 2, 3].isEmpty   -- false
#eval ([] : List Nat).isEmpty    -- true

-- ■ List.contains --- 要素が含まれるか（BEq が必要）
#eval [1, 2, 3].contains 2   -- true
#eval [1, 2, 3].contains 5   -- false

-- ============================================
-- 13. 実践的な例: リストを組み合わせて使う
-- ============================================

-- 例1: 1~10 の偶数の合計
#eval (List.range 11).filter (· % 2 == 0) |>.foldl (· + ·) 0
-- 30   (0 + 2 + 4 + 6 + 8 + 10)
-- |> はパイプ演算子（F# や Elixir と同じ）。左の結果を右の関数に渡す。

-- 例2: 文字列リストを改行で結合
def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ joinWith sep xs

#eval joinWith ", " ["Alice", "Bob", "Charlie"]
-- "Alice, Bob, Charlie"

-- 例3: インデックス付きで表示
def numberedList (xs : List String) : List String :=
  myEnum xs |>.map (fun (i, s) => s!"{i + 1}. {s}")

#eval numberedList ["りんご", "バナナ", "みかん"]
-- ["1. りんご", "2. バナナ", "3. みかん"]

-- 例4: 2つのリストの内積（ドット積）
def dotProduct (xs ys : List Nat) : Nat :=
  (xs.zip ys).map (fun (a, b) => a * b) |>.foldl (· + ·) 0

#eval dotProduct [1, 2, 3] [4, 5, 6]   -- 32   (1*4 + 2*5 + 3*6)

-- 例5: リストの重複除去（簡易版）
def unique [BEq α] : List α -> List α
  | []     => []
  | h :: t => if t.contains h then unique t else h :: unique t

-- 注意: この実装は後ろの方を優先する（順序が変わることがある）
-- 標準ライブラリの List.eraseDups もある
#eval [1, 2, 3, 2, 1, 4].eraseDups   -- [3, 2, 1, 4]

-- 例6: 再帰でリストを反転（reverse の自作）
def myReverse : List α -> List α
  | []     => []
  | h :: t => myReverse t ++ [h]

#eval myReverse [1, 2, 3, 4, 5]   -- [5, 4, 3, 2, 1]
-- 注意: この実装は O(n^2)。効率的な実装はアキュムレータを使う:

def myReverseAcc (acc : List α) : List α -> List α
  | []     => acc
  | h :: t => myReverseAcc (h :: acc) t

#eval myReverseAcc [] [1, 2, 3, 4, 5]   -- [5, 4, 3, 2, 1]
-- こちらは O(n)。標準ライブラリの reverse もこの方式。

-- ============================================
-- 14. まとめ: よく使う操作の対応表
-- ============================================
-- | Lean 4            | Python           | JavaScript          | Rust                |
-- |--------------------|------------------|---------------------|---------------------|
-- | [1, 2, 3]          | [1, 2, 3]        | [1, 2, 3]           | vec![1, 2, 3]       |
-- | h :: t             | ---              | ---                 | ---                 |
-- | xs ++ ys           | xs + ys          | [...xs, ...ys]      | [xs, ys].concat()   |
-- | xs.map f           | map(f, xs)       | xs.map(f)           | xs.iter().map(f)    |
-- | xs.filter p        | filter(p, xs)    | xs.filter(p)        | xs.iter().filter(p) |
-- | xs.foldl f init    | reduce(f, xs, i) | xs.reduce(f, init)  | xs.iter().fold(i,f) |
-- | xs.head?           | xs[0] (unsafe)   | xs[0] (unsafe)      | xs.first()          |
-- | xs[i]?             | xs[i] (unsafe)   | xs[i] (unsafe)      | xs.get(i)           |
-- | xs.length          | len(xs)          | xs.length           | xs.len()            |
-- | xs.reverse         | xs[::-1]         | xs.reverse()        | xs.iter().rev()     |
-- | xs.zip ys          | zip(xs, ys)      | ---                 | xs.iter().zip(ys)   |
-- | xs.enum            | enumerate(xs)    | xs.entries()        | xs.iter().enumerate |
-- | List.range n       | range(n)         | Array(n).keys()     | 0..n                |
-- | List.replicate n x | [x] * n          | Array(n).fill(x)    | vec![x; n]          |
-- | xs.filterMap f     | list comp.       | xs.flatMap(f)       | xs.iter().filter_map|

end Tutorial04
