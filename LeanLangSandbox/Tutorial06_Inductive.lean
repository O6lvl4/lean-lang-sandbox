-- ============================================
-- Tutorial 06: 帰納型 (Inductive Types)
-- 他言語の enum / union / ADT に相当する Lean の最強機能
-- ============================================
-- 他言語経験者向けの対応表:
--   TypeScript: type Shape = { tag: "circle", r: number } | { tag: "rect", w: number, h: number }
--   Rust:       enum Shape { Circle(f64), Rect(f64, f64) }
--   Haskell:    data Shape = Circle Double | Rect Double Double
--   Lean 4:     inductive Shape where | circle (r : Float) | rect (w h : Float)
--
-- Lean の帰納型は上記すべてを包含し、さらに「証明」にも使える

namespace Tutorial06

-- ============================================
-- 第1章: シンプルな列挙型 (Simple Enums)
-- ============================================
-- まずはデータを持たない純粋な列挙型から始める
-- TypeScript の `type Season = "spring" | "summer" | "autumn" | "winter"` に相当

-- ----------------------------------------
-- 1.1 季節 (Season)
-- ----------------------------------------
-- `deriving Repr` をつけると #eval で表示できるようになる
-- Repr は他言語の toString / Debug trait / Show に相当
inductive Season where
  | spring  -- 春
  | summer  -- 夏
  | autumn  -- 秋
  | winter  -- 冬
  deriving Repr

-- #eval で値を確認してみよう
-- `Season.spring` のように「型名.コンストラクタ名」でアクセスする
#eval Season.spring   -- => Season.spring
#eval Season.winter   -- => Season.winter

-- open すると型名のプレフィックスを省略できる
-- (ただしスコープ内のみ有効)
open Season in
#eval autumn  -- => Season.autumn

-- パターンマッチで分岐する関数
-- 他言語の switch/match に相当するが、Lean では「全パターン網羅」が必須
def Season.toJapanese : Season → String
  | .spring => "春"
  | .summer => "夏"
  | .autumn => "秋"
  | .winter => "冬"

#eval Season.spring.toJapanese  -- => "春"
#eval Season.winter.toJapanese  -- => "冬"

-- 季節 → 平均気温を返す関数
def Season.avgTemp : Season → Int
  | .spring => 15
  | .summer => 30
  | .autumn => 18
  | .winter => 5

#eval Season.summer.avgTemp  -- => 30
#eval Season.winter.avgTemp  -- => 5

-- ----------------------------------------
-- 1.2 方向 (Direction)
-- ----------------------------------------
inductive Direction where
  | north
  | south
  | east
  | west
  deriving Repr

-- 反対方向を返す関数
def Direction.opposite : Direction → Direction
  | .north => .south
  | .south => .north
  | .east  => .west
  | .west  => .east

#eval Direction.north.opposite            -- => Direction.south
#eval Direction.north.opposite.opposite   -- => Direction.north (2回で元に戻る)

-- 方向を日本語にする関数
def Direction.toJapanese : Direction → String
  | .north => "北"
  | .south => "南"
  | .east  => "東"
  | .west  => "西"

#eval Direction.east.toJapanese   -- => "東"

-- ----------------------------------------
-- 1.3 色 (Color)
-- ----------------------------------------
-- RGB の原色を表す列挙型
inductive Color where
  | red
  | green
  | blue
  | yellow
  | white
  | black
  deriving Repr

-- 補色を返す(簡易版)
def Color.complement : Color → Color
  | .red    => .green
  | .green  => .red
  | .blue   => .yellow
  | .yellow => .blue
  | .white  => .black
  | .black  => .white

#eval Color.red.complement    -- => Color.green
#eval Color.blue.complement   -- => Color.yellow

-- 色を16進数文字列に変換 (CSS風)
def Color.toHex : Color → String
  | .red    => "#FF0000"
  | .green  => "#00FF00"
  | .blue   => "#0000FF"
  | .yellow => "#FFFF00"
  | .white  => "#FFFFFF"
  | .black  => "#000000"

#eval Color.red.toHex     -- => "#FF0000"
#eval Color.yellow.toHex  -- => "#FFFF00"

-- ============================================
-- 第2章: データを持つ帰納型 (Inductive with Data)
-- ============================================
-- 列挙型の各バリアントがデータを保持できる
-- Rust の enum Shape { Circle(f64), Rect(f64, f64) } と同じ考え方

-- ----------------------------------------
-- 2.1 図形 (Shape)
-- ----------------------------------------
-- 各コンストラクタが異なる数・型のフィールドを持てる
inductive Shape where
  | circle    (radius : Float)              -- 円: 半径
  | rectangle (width : Float) (height : Float)  -- 長方形: 幅と高さ
  | triangle  (base : Float) (height : Float)   -- 三角形: 底辺と高さ
  deriving Repr

-- 面積を計算する関数
-- パターンマッチでコンストラクタの中身を取り出す
def Shape.area : Shape → Float
  | .circle r        => 3.14159265 * r * r      -- πr²
  | .rectangle w h   => w * h                  -- 幅×高さ
  | .triangle b h    => 0.5 * b * h            -- 底辺×高さ÷2

-- いくつかの図形を作って面積を計算
#eval Shape.circle 5.0 |>.area          -- => 78.539816... (π×25)
#eval Shape.rectangle 3.0 4.0 |>.area   -- => 12.000000
#eval Shape.triangle 6.0 4.0 |>.area    -- => 12.000000

-- 図形の説明を返す関数
def Shape.describe : Shape → String
  | .circle r      => s!"半径{r}の円"
  | .rectangle w h => s!"幅{w}×高さ{h}の長方形"
  | .triangle b h  => s!"底辺{b}×高さ{h}の三角形"

#eval Shape.circle 10.0 |>.describe        -- => "半径10.000000の円"
#eval Shape.rectangle 3.0 4.0 |>.describe  -- => "幅3.000000×高さ4.000000の長方形"

-- ----------------------------------------
-- 2.2 Option 型を自作してみる
-- ----------------------------------------
-- Lean の標準ライブラリにある Option は実はこうなっている:
--   inductive Option (α : Type) where
--     | none : Option α
--     | some : α → Option α
-- TypeScript の T | null、Rust の Option<T> に相当

-- 自作版 (名前をMyOptionにして衝突回避)
inductive MyOption (α : Type) where
  | none : MyOption α             -- 値がない
  | some : α → MyOption α         -- 値がある
  deriving Repr

-- MyOption から値を取り出す (デフォルト値付き)
def MyOption.getOrElse : MyOption α → α → α
  | .some x, _ => x     -- 値があればそれを返す
  | .none,   d => d     -- なければデフォルト値

#eval MyOption.some 42 |>.getOrElse 0     -- => 42
#eval MyOption.none |>.getOrElse (α := Nat) 0  -- => 0

-- ----------------------------------------
-- 2.3 Either / Result を自作
-- ----------------------------------------
-- 成功か失敗かを表す型
-- Rust の Result<T, E>、TypeScript の Either に相当
inductive MyResult (ε α : Type) where
  | ok  : α → MyResult ε α   -- 成功
  | err : ε → MyResult ε α   -- 失敗
  deriving Repr

def divide (x y : Nat) : MyResult String Nat :=
  if y == 0 then .err "ゼロ除算エラー"
  else .ok (x / y)

#eval divide 10 3   -- => MyResult.ok 3
#eval divide 10 0   -- => MyResult.err "ゼロ除算エラー"

-- ============================================
-- 第3章: 再帰的な帰納型 (Recursive Inductive Types)
-- ============================================
-- 帰納型の真の力: 自分自身を参照できる
-- これにより、木構造やリストなどの再帰的データ構造を定義できる

-- ----------------------------------------
-- 3.1 自然数をゼロから定義する (MyNat)
-- ----------------------------------------
-- Lean の組み込み Nat は実はこう定義されている:
--   inductive Nat where
--     | zero : Nat       -- 0
--     | succ : Nat → Nat -- n+1
-- つまり: 0 = zero, 1 = succ zero, 2 = succ (succ zero), ...
-- ペアノの公理そのもの！

-- 自作版
inductive MyNat where
  | zero : MyNat                -- 0
  | succ : MyNat → MyNat       -- n の次の数 (n+1)
  deriving Repr

-- 具体的な数を作ってみる
def myZero  : MyNat := .zero                          -- 0
def myOne   : MyNat := .succ .zero                    -- 1
def myTwo   : MyNat := .succ (.succ .zero)            -- 2
def myThree : MyNat := .succ (.succ (.succ .zero))    -- 3

#eval myZero   -- => MyNat.zero
#eval myOne    -- => MyNat.succ (MyNat.zero)
#eval myThree  -- => MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero)))

-- 通常の Nat に変換する関数
def MyNat.toNat : MyNat → Nat
  | .zero   => 0
  | .succ n => 1 + n.toNat  -- 再帰: 1 + (残りを変換)

#eval myZero.toNat   -- => 0
#eval myThree.toNat  -- => 3

-- Nat から MyNat に変換する関数
def MyNat.fromNat : Nat → MyNat
  | 0     => .zero
  | n + 1 => .succ (MyNat.fromNat n)

#eval (MyNat.fromNat 5).toNat  -- => 5 (変換して戻すと元通り)

-- 足し算を再帰で定義
-- m + 0 = m
-- m + (n+1) = (m + n) + 1
def MyNat.add : MyNat → MyNat → MyNat
  | m, .zero   => m                        -- m + 0 = m
  | m, .succ n => .succ (MyNat.add m n)    -- m + (n+1) = (m+n) + 1

#eval (MyNat.add myTwo myThree).toNat  -- => 5 (2 + 3 = 5)

-- 掛け算を再帰で定義
-- m * 0 = 0
-- m * (n+1) = m * n + m
def MyNat.mul : MyNat → MyNat → MyNat
  | _, .zero   => .zero                         -- m * 0 = 0
  | m, .succ n => MyNat.add (MyNat.mul m n) m   -- m * (n+1) = m*n + m

#eval (MyNat.mul myTwo myThree).toNat  -- => 6 (2 * 3 = 6)
#eval (MyNat.mul myThree myThree).toNat  -- => 9 (3 * 3 = 9)

-- 比較 (小なりイコール)
def MyNat.le : MyNat → MyNat → Bool
  | .zero,   _        => true    -- 0 <= 任意の数
  | .succ _, .zero    => false   -- n+1 > 0
  | .succ m, .succ n  => MyNat.le m n  -- succ m <= succ n ⟺ m <= n

#eval MyNat.le myTwo myThree   -- => true  (2 <= 3)
#eval MyNat.le myThree myTwo   -- => false (3 <= 2 は偽)
#eval MyNat.le myTwo myTwo     -- => true  (2 <= 2)

-- ----------------------------------------
-- 3.2 連結リスト (Linked List)
-- ----------------------------------------
-- Lean の組み込み List は実はこう定義されている:
--   inductive List (α : Type) where
--     | nil  : List α             -- 空リスト []
--     | cons : α → List α → List α  -- 要素 :: 残り
-- つまり: [1,2,3] = cons 1 (cons 2 (cons 3 nil))

-- 自作版
inductive MyList (α : Type) where
  | nil  : MyList α                    -- 空リスト
  | cons : α → MyList α → MyList α    -- 先頭要素 + 残りのリスト
  deriving Repr

-- 具体例を作る
def emptyList : MyList Nat := .nil
def list123 : MyList Nat := .cons 1 (.cons 2 (.cons 3 .nil))

#eval emptyList  -- => MyList.nil
#eval list123    -- => MyList.cons 1 (MyList.cons 2 (MyList.cons 3 (MyList.nil)))

-- リストの長さ
def MyList.length : MyList α → Nat
  | .nil       => 0
  | .cons _ xs => 1 + xs.length  -- 1 + 残りの長さ

#eval list123.length   -- => 3
#eval emptyList.length -- => 0

-- リストの合計 (Nat 専用)
def MyList.sum : MyList Nat → Nat
  | .nil       => 0
  | .cons x xs => x + xs.sum

#eval list123.sum  -- => 6 (1 + 2 + 3)

-- map: 各要素に関数を適用
def MyList.map (f : α → β) : MyList α → MyList β
  | .nil       => .nil
  | .cons x xs => .cons (f x) (xs.map f)

#eval list123.map (· * 10)  -- => MyList.cons 10 (MyList.cons 20 (MyList.cons 30 (MyList.nil)))

-- filter: 条件を満たす要素だけ残す
def MyList.filter (p : α → Bool) : MyList α → MyList α
  | .nil       => .nil
  | .cons x xs => if p x then .cons x (xs.filter p) else xs.filter p

-- 偶数だけ残す
#eval list123.filter (· % 2 == 0)  -- => MyList.cons 2 (MyList.nil)

-- 2つのリストを連結
def MyList.append : MyList α → MyList α → MyList α
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

def list45 : MyList Nat := .cons 4 (.cons 5 .nil)
#eval (list123.append list45).length  -- => 5

-- リストを反転
def MyList.reverse : MyList α → MyList α
  | .nil       => .nil
  | .cons x xs => xs.reverse.append (.cons x .nil)

-- 通常の List に変換して読みやすくする
def MyList.toList : MyList α → List α
  | .nil       => []
  | .cons x xs => x :: xs.toList

#eval list123.toList            -- => [1, 2, 3]
#eval list123.reverse.toList    -- => [3, 2, 1]
#eval (list123.append list45).toList  -- => [1, 2, 3, 4, 5]

-- ----------------------------------------
-- 3.3 二分木 (Binary Tree)
-- ----------------------------------------
-- 各ノードが値を持ち、左右の子を持つ再帰的なデータ構造
inductive BinTree (α : Type) where
  | leaf : BinTree α                                    -- 葉 (空)
  | node : BinTree α → α → BinTree α → BinTree α      -- 左の子, 値, 右の子
  deriving Repr

-- 具体的な木を作る
--        3
--       / \
--      1   5
--     / \ / \
--    .  2 4  .
-- (. は leaf)
def sampleTree : BinTree Nat :=
  .node
    (.node .leaf 1 (.node .leaf 2 .leaf))
    3
    (.node (.node .leaf 4 .leaf) 5 .leaf)

-- ノード数を数える
def BinTree.size : BinTree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + l.size + r.size

#eval sampleTree.size  -- => 5

-- 木の深さ(高さ)を求める
def BinTree.depth : BinTree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + max l.depth r.depth

#eval sampleTree.depth  -- => 3

-- 中間順走査 (in-order traversal): 左 → 自分 → 右
-- 二分探索木なら、ソートされた結果が得られる
def BinTree.inorder : BinTree α → List α
  | .leaf       => []
  | .node l v r => l.inorder ++ [v] ++ r.inorder

#eval sampleTree.inorder  -- => [1, 2, 3, 4, 5] (ソート済み!)

-- 前順走査 (pre-order): 自分 → 左 → 右
def BinTree.preorder : BinTree α → List α
  | .leaf       => []
  | .node l v r => [v] ++ l.preorder ++ r.preorder

#eval sampleTree.preorder  -- => [3, 1, 2, 5, 4]

-- 木の全要素に関数を適用 (map)
def BinTree.map (f : α → β) : BinTree α → BinTree β
  | .leaf       => .leaf
  | .node l v r => .node (l.map f) (f v) (r.map f)

#eval (sampleTree.map (· * 100)).inorder  -- => [100, 200, 300, 400, 500]

-- 要素が含まれるか検索 (BEq が必要)
def BinTree.contains [BEq α] (x : α) : BinTree α → Bool
  | .leaf       => false
  | .node l v r => x == v || l.contains x || r.contains x

#eval sampleTree.contains 3  -- => true
#eval sampleTree.contains 7  -- => false

-- 二分探索木への挿入 (Ord が必要)
-- すでに同じ値があれば何もしない
def BinTree.insert [Ord α] (x : α) : BinTree α → BinTree α
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    match compare x v with
    | .lt => .node (l.insert x) v r   -- x < v なら左に挿入
    | .eq => .node l v r              -- x == v なら何もしない
    | .gt => .node l v (r.insert x)   -- x > v なら右に挿入

-- 空の木にどんどん挿入してみる
def buildTree : BinTree Nat :=
  BinTree.leaf |>.insert 5 |>.insert 3 |>.insert 7 |>.insert 1 |>.insert 4

#eval buildTree.inorder  -- => [1, 3, 4, 5, 7] (ソートされている)

-- ----------------------------------------
-- 3.4 式の木 (Expression Tree) - 簡易電卓
-- ----------------------------------------
-- 四則演算の式を木構造で表現する
-- これはインタプリタやコンパイラの基礎
inductive Expr where
  | num : Int → Expr                     -- 数値リテラル
  | add : Expr → Expr → Expr            -- 足し算
  | sub : Expr → Expr → Expr            -- 引き算
  | mul : Expr → Expr → Expr            -- 掛け算
  | div : Expr → Expr → Expr            -- 割り算
  | neg : Expr → Expr                   -- 符号反転 (-x)
  deriving Repr

-- 式を評価する関数 (簡易電卓の核心)
-- ゼロ除算は 0 を返す簡略化
def Expr.eval : Expr → Int
  | .num n     => n
  | .add e1 e2 => e1.eval + e2.eval
  | .sub e1 e2 => e1.eval - e2.eval
  | .mul e1 e2 => e1.eval * e2.eval
  | .div e1 e2 =>
    let d := e2.eval
    if d == 0 then 0 else e1.eval / d
  | .neg e     => -e.eval

-- (2 + 3) * 4 を表現して評価
-- 木構造:
--      *
--     / \
--    +   4
--   / \
--  2   3
def expr1 : Expr := .mul (.add (.num 2) (.num 3)) (.num 4)
#eval expr1.eval  -- => 20 ((2+3)*4 = 20)

-- (10 - 3) * (1 + 1) を表現して評価
def expr2 : Expr := .mul (.sub (.num 10) (.num 3)) (.add (.num 1) (.num 1))
#eval expr2.eval  -- => 14 ((10-3)*(1+1) = 14)

-- -(5 + 3)
def expr3 : Expr := .neg (.add (.num 5) (.num 3))
#eval expr3.eval  -- => -8

-- 式を人間が読める文字列に変換
def Expr.toString : Expr → String
  | .num n     => s!"{n}"
  | .add e1 e2 => s!"({e1.toString} + {e2.toString})"
  | .sub e1 e2 => s!"({e1.toString} - {e2.toString})"
  | .mul e1 e2 => s!"({e1.toString} * {e2.toString})"
  | .div e1 e2 => s!"({e1.toString} / {e2.toString})"
  | .neg e     => s!"(-{e.toString})"

#eval expr1.toString  -- => "((2 + 3) * 4)"
#eval expr2.toString  -- => "((10 - 3) * (1 + 1))"
#eval expr3.toString  -- => "(-(5 + 3))"

-- 式に含まれるノード数 (式の複雑さの指標)
def Expr.nodeCount : Expr → Nat
  | .num _     => 1
  | .add e1 e2 => 1 + e1.nodeCount + e2.nodeCount
  | .sub e1 e2 => 1 + e1.nodeCount + e2.nodeCount
  | .mul e1 e2 => 1 + e1.nodeCount + e2.nodeCount
  | .div e1 e2 => 1 + e1.nodeCount + e2.nodeCount
  | .neg e     => 1 + e.nodeCount

#eval expr1.nodeCount  -- => 5 (mul, add, 2, 3, 4)

-- 定数畳み込み (式の最適化の一例)
-- 0 + x = x, x + 0 = x, 0 * x = 0, 1 * x = x のようなルールで簡略化
def Expr.simplify : Expr → Expr
  | .add (.num 0) e => e.simplify           -- 0 + x = x
  | .add e (.num 0) => e.simplify           -- x + 0 = x
  | .mul (.num 0) _ => .num 0               -- 0 * x = 0
  | .mul _ (.num 0) => .num 0               -- x * 0 = 0
  | .mul (.num 1) e => e.simplify           -- 1 * x = x
  | .mul e (.num 1) => e.simplify           -- x * 1 = x
  | .neg (.neg e)   => e.simplify           -- --x = x
  | .add e1 e2      => .add e1.simplify e2.simplify
  | .sub e1 e2      => .sub e1.simplify e2.simplify
  | .mul e1 e2      => .mul e1.simplify e2.simplify
  | .div e1 e2      => .div e1.simplify e2.simplify
  | .neg e          => .neg e.simplify
  | e               => e

-- 0 + (1 * x) を簡略化: x
def exprToSimplify : Expr := .add (.num 0) (.mul (.num 1) (.num 42))
#eval exprToSimplify.toString           -- => "(0 + (1 * 42))"
#eval exprToSimplify.simplify.toString  -- => "42"
#eval exprToSimplify.simplify.eval      -- => 42

-- ============================================
-- 第4章: パターンマッチの高度な使い方
-- ============================================

-- ----------------------------------------
-- 4.1 ネストしたパターンマッチ
-- ----------------------------------------
-- パターンの中でさらにパターンマッチできる

-- 2つの季節の組み合わせで旅行先を決める
def travelDestination : Season × Season → String
  | (.spring, .spring) => "京都 (桜が満開)"
  | (.summer, .summer) => "北海道 (涼しい)"
  | (.winter, _)       => "沖縄 (冬は暖かい場所へ)"
  | (_, .winter)       => "沖縄 (冬は暖かい場所へ)"
  | _                  => "東京 (いつでも楽しい)"

#eval travelDestination (.spring, .spring)  -- => "京都 (桜が満開)"
#eval travelDestination (.winter, .summer)  -- => "沖縄 (冬は暖かい場所へ)"
#eval travelDestination (.autumn, .summer)  -- => "東京 (いつでも楽しい)"

-- ----------------------------------------
-- 4.2 match 式 (関数定義以外でのパターンマッチ)
-- ----------------------------------------
-- 関数定義だけでなく、式の途中でも match が使える
def describeNumber (n : Nat) : String :=
  match n with
  | 0     => "ゼロ"
  | 1     => "いち"
  | 2     => "に"
  | 3     => "さん"
  | n + 1 => s!"{n + 1}は大きい数"  -- 4以上

#eval describeNumber 0   -- => "ゼロ"
#eval describeNumber 3   -- => "さん"
#eval describeNumber 42  -- => "42は大きい数"

-- ----------------------------------------
-- 4.3 if let パターン (Option の分解に便利)
-- ----------------------------------------
-- Option 型のパターンマッチをコンパクトに書ける
def greet (name : Option String) : String :=
  -- match でも書ける:
  -- match name with
  -- | some n => s!"こんにちは、{n}さん!"
  -- | none   => "こんにちは、ゲストさん!"
  if let some n := name then
    s!"こんにちは、{n}さん!"
  else
    "こんにちは、ゲストさん!"

#eval greet (some "太郎")  -- => "こんにちは、太郎さん!"
#eval greet none           -- => "こんにちは、ゲストさん!"

-- ============================================
-- 第5章: 再帰関数のパターン集
-- ============================================
-- 帰納型 + パターンマッチ + 再帰 = 関数型プログラミングの三種の神器

-- ----------------------------------------
-- 5.1 フィボナッチ数列 (自然数の再帰)
-- ----------------------------------------
def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci (n + 1) + fibonacci n  -- F(n+2) = F(n+1) + F(n)

#eval (List.range 10).map fibonacci  -- => [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

-- ----------------------------------------
-- 5.2 リストに対する再帰パターン集
-- ----------------------------------------
-- 以下は Lean の組み込み List に対する再帰関数の例

-- リストの最大値を求める (空リストは 0)
def listMax : List Nat → Nat
  | []      => 0
  | [x]     => x
  | x :: xs => max x (listMax xs)

#eval listMax [3, 1, 4, 1, 5, 9, 2, 6]  -- => 9

-- リストを畳み込む (foldl を自作)
def myFoldl (f : β → α → β) (init : β) : List α → β
  | []      => init
  | x :: xs => myFoldl f (f init x) xs

-- foldl で合計を求める
#eval myFoldl (· + ·) 0 [1, 2, 3, 4, 5]  -- => 15

-- foldl で文字列を連結
#eval myFoldl (· ++ · ++ " ") "" ["Lean", "4", "is", "cool"]
  -- => "Lean 4 is cool "

-- zip: 2つのリストを組にする
def myZip : List α → List β → List (α × β)
  | [],      _       => []
  | _,       []      => []
  | x :: xs, y :: ys => (x, y) :: myZip xs ys

#eval myZip [1, 2, 3] ["a", "b", "c"]  -- => [(1, "a"), (2, "b"), (3, "c")]

-- take: リストの先頭 n 要素を取る
def myTake : Nat → List α → List α
  | 0,     _        => []
  | _,     []       => []
  | n + 1, x :: xs  => x :: myTake n xs

#eval myTake 3 [10, 20, 30, 40, 50]  -- => [10, 20, 30]

-- ============================================
-- 第6章: deriving Repr の詳細
-- ============================================
-- `deriving Repr` は #eval や #print で型の値を表示するために必要
-- 他言語の対応:
--   Rust:    #[derive(Debug)]
--   Haskell: deriving Show
--   Python:  __repr__

-- deriving なしだとどうなるか?
inductive NoRepr where
  | hello
  | world

-- 以下をアンコメントするとエラーになる:
-- #eval NoRepr.hello  -- error: don't know how to synthesize placeholder context

-- deriving Repr を後付けで追加することもできる
deriving instance Repr for NoRepr

-- これで表示できるようになる!
#eval NoRepr.hello  -- => NoRepr.hello

-- 複数の型クラスを同時に derive できる
inductive Priority where
  | low
  | medium
  | high
  deriving Repr, BEq, Ord

-- BEq: 等値比較ができるようになる
#eval (Priority.low == Priority.low)     -- => true
#eval (Priority.low == Priority.high)    -- => false

-- Ord: 比較 (大小関係) ができるようになる
-- low < medium < high の順になる (コンストラクタの定義順)

-- ============================================
-- 第7章: Lean 組み込み型との関係
-- ============================================
-- ここまで自作してきた型は、実は Lean の標準ライブラリにあるものと同じ構造

-- ----------------------------------------
-- 7.1 Nat (自然数)
-- ----------------------------------------
-- 組み込みの Nat は MyNat とまったく同じ構造:
--   inductive Nat where
--     | zero : Nat
--     | succ (n : Nat) : Nat
-- ただし、Lean は内部で効率的なバイナリ表現を使う

-- Nat のコンストラクタを直接使ってみる
#eval Nat.zero               -- => 0
#eval Nat.succ Nat.zero      -- => 1
#eval Nat.succ (Nat.succ Nat.zero)  -- => 2
-- 数値リテラル 42 は実は Nat.succ (Nat.succ (... Nat.zero ...)) の糖衣構文!

-- パターンマッチで Nat の構造を見る
def isZero : Nat → Bool
  | .zero   => true
  | .succ _ => false

#eval isZero 0   -- => true
#eval isZero 5   -- => false

-- predecessor: 前の数 (0 の前は 0)
def pred : Nat → Nat
  | .zero   => .zero
  | .succ n => n

#eval pred 5   -- => 4
#eval pred 0   -- => 0

-- ----------------------------------------
-- 7.2 List (リスト)
-- ----------------------------------------
-- 組み込みの List は MyList とまったく同じ構造:
--   inductive List (α : Type) where
--     | nil  : List α
--     | cons (head : α) (tail : List α) : List α
-- [] は nil の糖衣構文
-- x :: xs は cons x xs の糖衣構文
-- [1, 2, 3] は 1 :: 2 :: 3 :: [] の糖衣構文

-- コンストラクタを直接使ってみる
#eval List.nil (α := Nat)                               -- => []
#eval List.cons 1 (List.cons 2 (List.cons 3 List.nil))  -- => [1, 2, 3]
-- ↑ これは [1, 2, 3] とまったく同じ!

-- パターンマッチでリストを分解
def myHead? : List α → Option α
  | []      => none        -- nil の糖衣構文
  | x :: _  => some x      -- cons x _ の糖衣構文

#eval myHead? [10, 20, 30]   -- => some 10
#eval myHead? ([] : List Nat) -- => none

-- ----------------------------------------
-- 7.3 Option
-- ----------------------------------------
-- 組み込みの Option:
--   inductive Option (α : Type) where
--     | none : Option α
--     | some (val : α) : Option α
-- MyOption とまったく同じ!

#eval Option.none (α := Nat)  -- => none
#eval Option.some 42          -- => some 42

-- ----------------------------------------
-- 7.4 Bool も帰納型!
-- ----------------------------------------
-- 実は Bool すら帰納型:
--   inductive Bool where
--     | false : Bool
--     | true  : Bool
-- true/false は Bool.true/Bool.false の糖衣構文

-- ----------------------------------------
-- 7.5 And, Or も帰納型 (命題としての論理)
-- ----------------------------------------
-- 論理積 (∧):
--   inductive And (a b : Prop) : Prop where
--     | intro (left : a) (right : b) : And a b
-- 論理和 (∨):
--   inductive Or (a b : Prop) : Prop where
--     | inl (h : a) : Or a b
--     | inr (h : b) : Or a b
-- つまり Lean では「論理」すら帰納型で定義されている!

-- ============================================
-- 第8章: 相互再帰型 (Mutual Inductive)
-- ============================================
-- 2つ以上の型が互いに参照し合う場合

-- JSON のような構造を表現する例
-- Value が Array (= List Value) を含み、
-- Array が Value を含むので相互再帰になる
inductive JsonValue where
  | null   : JsonValue
  | bool   : Bool → JsonValue
  | num    : Float → JsonValue
  | str    : String → JsonValue
  | array  : List JsonValue → JsonValue
  | object : List (String × JsonValue) → JsonValue
  deriving Repr

-- JSON値を文字列に変換 (簡易版)
partial def JsonValue.format : JsonValue → String
  | .null     => "null"
  | .bool b   => if b then "true" else "false"
  | .num n    => s!"{n}"
  | .str s    => s!"\"{s}\""
  | .array xs =>
    let items := xs.map JsonValue.format
    "[" ++ String.intercalate ", " items ++ "]"
  | .object kvs =>
    let items := kvs.map fun (k, v) => s!"\"{k}\": {v.format}"
    "{" ++ String.intercalate ", " items ++ "}"

-- JSON のサンプルデータ
def sampleJson : JsonValue :=
  .object [
    ("name", .str "太郎"),
    ("age", .num 25.0),
    ("active", .bool true),
    ("scores", .array [.num 85.0, .num 92.0, .num 78.0]),
    ("address", .null)
  ]

#eval sampleJson.format
  -- => {"name": "太郎", "age": 25.000000, "active": true, "scores": [85.000000, 92.000000, 78.000000], "address": null}

-- ============================================
-- まとめ
-- ============================================
-- 帰納型 (Inductive Types) は Lean 4 の最も基本的な型定義メカニズム
--
-- 1. シンプルな列挙型:       データなしのバリアント (Season, Direction)
-- 2. データ付き帰納型:       各バリアントが値を持つ (Shape, MyResult)
-- 3. 再帰的帰納型:           自分自身を参照する (MyNat, MyList, BinTree, Expr)
-- 4. パラメトリック帰納型:   型パラメータを持つ (MyList α, BinTree α)
-- 5. 相互再帰型:             複数の型が互いに参照する (JsonValue)
--
-- Lean の哲学: すべてのデータ構造は帰納型から構築される
--   - Nat, List, Option, Bool, さらには論理演算子 (And, Or) まで
--   - 「型を定義する」=「帰納型を定義する」と言っても過言ではない
--
-- 他言語との対応:
--   TypeScript: tagged union + switch
--   Rust:       enum + match
--   Haskell:    data + case
--   Lean 4:     inductive + pattern matching
--
-- 次のステップ:
--   - 構造体 (structure) = フィールドが1つのコンストラクタだけの帰納型
--   - 型クラス (class) = 構造体 + 自動解決
--   - 依存型 (dependent types) = 型の中に値が登場する帰納型

end Tutorial06
