-- ============================================
-- Lean 4 型クラス (Type Classes) チュートリアル
-- 他言語の interface / trait に相当する仕組み
-- ============================================

namespace Tutorial07

-- ============================================
-- 目次
-- 1. 型クラスとは何か
-- 2. class でインターフェースを定義する
-- 3. instance で実装を与える
-- 4. 組み込み型クラス一覧
-- 5. カスタム型に ToString を実装する
-- 6. カスタム型に BEq を実装する
-- 7. カスタム型に Ord を実装する
-- 8. 型クラス制約を使ったジェネリック関数
-- 9. deriving で自動導出する
-- 10. 実践例: Card 型をソート可能・表示可能にする
-- ============================================


-- ============================================
-- 1. 型クラスとは何か
-- ============================================

-- 型クラスは、ある型が「どんな操作をサポートしているか」を抽象的に表す仕組み。
--
-- 他の言語との対応:
--   Java / C#     → interface
--   Rust           → trait
--   Haskell        → type class (Lean の直接の元ネタ)
--   TypeScript     → interface
--   Go             → interface (暗黙実装)
--
-- 例えば「文字列に変換できる」という能力は ToString 型クラスで表現される。
-- ある型 T に対して ToString T のインスタンスを定義すると、
-- toString 関数がその型 T に対して使えるようになる。


-- ============================================
-- 2. class でインターフェースを定義する
-- ============================================

-- まずは自分で型クラスを定義してみよう。
-- 「挨拶できる」という能力を型クラスで表現する。

class Greetable (α : Type) where
  greet : α → String

-- 解説:
-- class キーワードで型クラスを定義する。
-- α は型パラメータ。任意の型に対してこのインターフェースを実装できる。
-- greet はメソッド。α の値を受け取って String を返す。


-- ============================================
-- 3. instance で実装を与える
-- ============================================

-- まずは簡単な型を用意する
structure Person where
  name : String
  age : Nat

-- Person 型に Greetable を実装する
instance : Greetable Person where
  greet p := s!"こんにちは、{p.name}さん（{p.age}歳）です！"

-- 使ってみる
#eval Greetable.greet (Person.mk "太郎" 25)
-- => "こんにちは、太郎さん（25歳）です！"

-- String にも Greetable を実装できる
instance : Greetable String where
  greet s := s!"Hello, {s}!"

#eval Greetable.greet "World"
-- => "Hello, World!"

-- Nat にも実装できる（なんでも型クラスのインスタンスにできる）
instance : Greetable Nat where
  greet n := s!"数値 {n} が挨拶します！"

#eval Greetable.greet 42
-- => "数値 42 が挨拶します！"


-- ============================================
-- 4. 組み込み型クラス一覧
-- ============================================

-- Lean 4 にはよく使う型クラスが最初から定義されている。
-- 主要なものを紹介する。

-- ----------------------------------------
-- 4.1 ToString : 文字列への変換
-- ----------------------------------------
-- toString 関数を提供する。IO.println で表示するときなどに使われる。

#eval toString 42          -- "42"
#eval toString true        -- "true"
#eval toString [1, 2, 3]   -- "[1, 2, 3]"

-- ----------------------------------------
-- 4.2 Repr : デバッグ用の表現
-- ----------------------------------------
-- #eval で値を表示するときに使われる内部表現。
-- toString よりも詳細な情報を出すことが多い。

#eval repr 42              -- 42
#eval repr "hello"         -- "\"hello\""
#eval repr [1, 2, 3]       -- [1, 2, 3]

-- ----------------------------------------
-- 4.3 BEq : 等値比較 (== 演算子)
-- ----------------------------------------
-- == と != を使うために必要。
-- BEq は Boolean Equality の略。

#eval (1 == 1 : Bool)      -- true
#eval (1 == 2 : Bool)      -- false
#eval ("abc" == "abc")     -- true
#eval ("abc" != "xyz")     -- true

-- ----------------------------------------
-- 4.4 Ord : 順序比較
-- ----------------------------------------
-- compare 関数と <, >, <=, >= 演算子を提供する。
-- compare は Ordering 型（lt, eq, gt）を返す。

#eval compare 1 2          -- Ordering.lt  （1 < 2）
#eval compare 5 5          -- Ordering.eq  （5 == 5）
#eval compare 9 3          -- Ordering.gt  （9 > 3）
#eval (3 < 5 : Bool)       -- true
#eval ("abc" < "abd")      -- true （辞書順）

-- ----------------------------------------
-- 4.5 Inhabited : デフォルト値を持つ
-- ----------------------------------------
-- 「この型にはデフォルト値がある」ことを示す。
-- default でデフォルト値を取得できる。

#eval (default : Nat)      -- 0
#eval (default : String)   -- ""
#eval (default : Bool)     -- false

-- ----------------------------------------
-- 4.6 Add : 加算演算子 (+)
-- ----------------------------------------
-- + 演算子を使うために必要。

#eval (3 + 5 : Nat)        -- 8
#eval (1.5 + 2.5 : Float)  -- 4.000000

-- ----------------------------------------
-- 4.7 Mul : 乗算演算子 (*)
-- ----------------------------------------
-- * 演算子を使うために必要。

#eval (3 * 5 : Nat)        -- 15
#eval (2.0 * 3.5 : Float)  -- 7.000000


-- ============================================
-- 5. カスタム型に ToString を実装する
-- ============================================

-- 色を表す型
inductive Color where
  | red
  | green
  | blue
  | rgb (r g b : Nat)

-- Color に ToString を実装する
instance : ToString Color where
  toString c := match c with
    | Color.red     => "赤"
    | Color.green   => "緑"
    | Color.blue    => "青"
    | Color.rgb r g b => s!"RGB({r}, {g}, {b})"

-- 使ってみる
#eval toString Color.red             -- "赤"
#eval toString Color.green           -- "緑"
#eval toString (Color.rgb 255 128 0) -- "RGB(255, 128, 0)"

-- s! 文字列補間の中でも自動的に toString が呼ばれる
#eval s!"空の色は{Color.blue}です"   -- "空の色は青です"

-- リストの要素にも使われる（List の ToString は要素の ToString を利用する）
#eval toString [Color.red, Color.green, Color.blue]
-- => "[赤, 緑, 青]"

-- もう一つの例: 2Dの点
structure Point where
  x : Float
  y : Float

instance : ToString Point where
  toString p := s!"({p.x}, {p.y})"

#eval toString (Point.mk 3.0 4.0)   -- "(3.000000, 4.000000)"


-- ============================================
-- 6. カスタム型に BEq を実装する
-- ============================================

-- 方角の型
inductive Direction where
  | north
  | south
  | east
  | west

-- BEq を手動で実装する
instance : BEq Direction where
  beq a b := match a, b with
    | Direction.north, Direction.north => true
    | Direction.south, Direction.south => true
    | Direction.east,  Direction.east  => true
    | Direction.west,  Direction.west  => true
    | _, _                             => false

-- == が使えるようになった！
#eval (Direction.north == Direction.north)  -- true
#eval (Direction.north == Direction.south)  -- false
#eval (Direction.east != Direction.west)    -- true

-- 構造体の場合: 全フィールドを比較する
instance : BEq Point where
  beq a b := a.x == b.x && a.y == b.y

#eval (Point.mk 1.0 2.0 == Point.mk 1.0 2.0)  -- true
#eval (Point.mk 1.0 2.0 == Point.mk 3.0 4.0)  -- false


-- ============================================
-- 7. カスタム型に Ord を実装する
-- ============================================

-- 温度を表す型
structure Temperature where
  celsius : Float
deriving BEq  -- BEq は deriving で自動導出（後述）

-- Ord を手動実装する
-- compare メソッドを定義する必要がある
instance : Ord Temperature where
  compare a b :=
    if a.celsius < b.celsius then .lt
    else if a.celsius > b.celsius then .gt
    else .eq

-- ToString も付けておく
instance : ToString Temperature where
  toString t := s!"{t.celsius}°C"

-- compare が使える
#eval compare (Temperature.mk 20.0) (Temperature.mk 30.0)
-- => Ordering.lt  （20°C < 30°C）

#eval compare (Temperature.mk 100.0) (Temperature.mk 50.0)
-- => Ordering.gt  （100°C > 50°C）

-- もう少し複雑な例: 優先度付きのタスク
-- 優先度が高い(数値が小さい)ほど先に来る
structure TodoTask where
  priority : Nat
  title : String

instance : BEq TodoTask where
  beq a b := a.priority == b.priority && a.title == b.title

instance : Ord TodoTask where
  compare a b :=
    -- まず優先度で比較。同じなら名前で比較
    match compare a.priority b.priority with
    | Ordering.eq => compare a.title b.title
    | ord         => ord

instance : ToString TodoTask where
  toString t := s!"[P{t.priority}] {t.title}"

-- 比較してみる
#eval compare (TodoTask.mk 1 "緊急バグ修正") (TodoTask.mk 3 "リファクタリング")
-- => Ordering.lt  (優先度1 < 優先度3 なので lt)

-- ソートに使う（Lean の List.mergeSort は Ord を利用できる）
def tasks : List TodoTask := [
  TodoTask.mk 3 "リファクタリング",
  TodoTask.mk 1 "緊急バグ修正",
  TodoTask.mk 2 "新機能追加",
  TodoTask.mk 1 "セキュリティパッチ"
]

-- List.mergeSort で比較関数を渡してソートする
def sortedTasks : List TodoTask :=
  tasks.mergeSort (fun a b => compare a b != Ordering.gt)

#eval sortedTasks.map toString
-- => ["[P1] セキュリティパッチ", "[P1] 緊急バグ修正", "[P2] 新機能追加", "[P3] リファクタリング"]


-- ============================================
-- 8. 型クラス制約を使ったジェネリック関数
-- ============================================

-- 型クラスの真価は「ジェネリックな関数」を書けること。
-- [制約] という構文で型クラス制約を指定する。

-- ----------------------------------------
-- 8.1 基本: 任意の Ord 型で使える max 関数
-- ----------------------------------------
def maxOf [Ord α] (a b : α) : α :=
  if compare a b == .gt then a else b

-- Nat で使える
#eval maxOf 10 20          -- 20

-- String で使える（辞書順で大きい方）
#eval maxOf "apple" "banana"  -- "banana"

-- Temperature でも使える（Ord を実装したので）
#eval toString (maxOf (Temperature.mk 36.5) (Temperature.mk 38.0))
-- => "38.000000°C"

-- ----------------------------------------
-- 8.2 複数の制約を同時に指定する
-- ----------------------------------------
-- [制約1] [制約2] ... のように並べる

-- 「等値比較ができて文字列に変換できる型」に対する関数
def showEqual [BEq α] [ToString α] (a b : α) : String :=
  if a == b then
    s!"{a} と {b} は等しい"
  else
    s!"{a} と {b} は等しくない"

#eval showEqual 42 42           -- "42 と 42 は等しい"
#eval showEqual "hello" "world" -- "hello と world は等しくない"

-- ----------------------------------------
-- 8.3 リストに対するジェネリック関数
-- ----------------------------------------

-- リストの最大値を求める（空リストなら default を返す）
def listMax [Ord α] [Inhabited α] (xs : List α) : α :=
  match xs with
  | []      => default
  | [x]     => x
  | x :: rest => maxOf x (listMax rest)

#eval listMax [3, 1, 4, 1, 5, 9, 2, 6]  -- 9
#eval listMax ["cat", "dog", "bird"]     -- "dog" （辞書順）

-- リスト内に特定の要素があるかチェック
def contains [BEq α] (xs : List α) (target : α) : Bool :=
  match xs with
  | []     => false
  | x :: rest => x == target || contains rest target

#eval contains [1, 2, 3, 4, 5] 3   -- true
#eval contains [1, 2, 3, 4, 5] 9   -- false
#eval contains ["a", "b", "c"] "b"  -- true

-- ----------------------------------------
-- 8.4 型クラス制約を使った高度な例
-- ----------------------------------------

-- 2つの値を足して文字列で返す関数
-- Add と ToString の両方が必要
def addAndShow [Add α] [ToString α] (a b : α) : String :=
  s!"{a} + {b} = {a + b}"

#eval addAndShow 3 5           -- "3 + 5 = 8"
#eval addAndShow 1.5 2.5       -- "1.500000 + 2.500000 = 4.000000"


-- ============================================
-- 9. deriving で自動導出する
-- ============================================

-- 手動で instance を書くのは面倒な場合がある。
-- deriving キーワードを使うと、コンパイラが自動的にインスタンスを生成してくれる。

-- ----------------------------------------
-- 9.1 構造体での deriving
-- ----------------------------------------

structure Coordinate where
  lat : Float
  lng : Float
deriving Repr, BEq, Inhabited

-- Repr が自動導出されたので #eval で表示できる
#eval Coordinate.mk 35.6762 139.6503
-- => { lat := 35.676200, lng := 139.650300 }

-- BEq が自動導出されたので == が使える
#eval (Coordinate.mk 1.0 2.0 == Coordinate.mk 1.0 2.0)  -- true

-- Inhabited が自動導出されたので default がある
#eval (default : Coordinate)
-- => { lat := 0.000000, lng := 0.000000 }

-- ----------------------------------------
-- 9.2 帰納型 (inductive) での deriving
-- ----------------------------------------

inductive Season where
  | spring
  | summer
  | autumn
  | winter
deriving Repr, BEq, Inhabited

-- Repr で表示できる
#eval Season.spring             -- Tutorial07_TypeClasses.Season.spring
#eval Season.autumn             -- Tutorial07_TypeClasses.Season.autumn

-- BEq で比較できる
#eval (Season.spring == Season.spring)  -- true
#eval (Season.spring == Season.summer)  -- false

-- Inhabited のデフォルト値（最初のコンストラクタになる）
#eval (default : Season)        -- Tutorial07_TypeClasses.Season.spring

-- ----------------------------------------
-- 9.3 deriving と手動実装の使い分け
-- ----------------------------------------
-- deriving が便利なケース:
--   BEq → 全フィールド / 全コンストラクタの構造的等値でOKなとき
--   Repr → デバッグ用の表示で十分なとき
--   Inhabited → デフォルト値が自動で決まってよいとき
--
-- 手動実装が必要なケース:
--   ToString → ユーザーフレンドリーな表示をカスタマイズしたいとき
--   Ord → 独自の順序を定義したいとき
--   BEq → 一部のフィールドだけで比較したいとき


-- ============================================
-- 10. 実践例: Card 型をソート可能・表示可能にする
-- ============================================

-- ----------------------------------------
-- 10.1 型の定義
-- ----------------------------------------

-- トランプのスート (マーク)
inductive Suit where
  | spade
  | heart
  | diamond
  | club
deriving Repr, BEq

-- スートの強さ: spade > heart > diamond > club
-- (ブリッジの慣習に従う)
def Suit.toNat : Suit → Nat
  | .club    => 0
  | .diamond => 1
  | .heart   => 2
  | .spade   => 3

instance : Ord Suit where
  compare a b := compare a.toNat b.toNat

instance : ToString Suit where
  toString s := match s with
    | .spade   => "\u2660"   -- ♠
    | .heart   => "\u2665"   -- ♥
    | .diamond => "\u2666"   -- ♦
    | .club    => "\u2663"   -- ♣

-- トランプのランク (数字)
inductive Rank where
  | two | three | four | five | six | seven | eight | nine | ten
  | jack | queen | king | ace
deriving Repr, BEq

-- ランクの強さ: 2 < 3 < ... < 10 < J < Q < K < A
def Rank.toNat : Rank → Nat
  | .two   => 2
  | .three => 3
  | .four  => 4
  | .five  => 5
  | .six   => 6
  | .seven => 7
  | .eight => 8
  | .nine  => 9
  | .ten   => 10
  | .jack  => 11
  | .queen => 12
  | .king  => 13
  | .ace   => 14

instance : Ord Rank where
  compare a b := compare a.toNat b.toNat

instance : ToString Rank where
  toString r := match r with
    | .two   => "2"
    | .three => "3"
    | .four  => "4"
    | .five  => "5"
    | .six   => "6"
    | .seven => "7"
    | .eight => "8"
    | .nine  => "9"
    | .ten   => "10"
    | .jack  => "J"
    | .queen => "Q"
    | .king  => "K"
    | .ace   => "A"

-- カード = スート + ランク
structure Card where
  suit : Suit
  rank : Rank
deriving Repr

-- ----------------------------------------
-- 10.2 型クラスの実装
-- ----------------------------------------

-- ToString: 表示用
instance : ToString Card where
  toString c := s!"{c.suit}{c.rank}"

-- BEq: 等値比較（スートとランクが両方同じなら等しい）
instance : BEq Card where
  beq a b := a.suit == b.suit && a.rank == b.rank

-- Ord: 順序（まずランクで比較、同じならスートで比較）
-- ポーカーなどのゲームではランクが重要なので、ランクを優先
instance : Ord Card where
  compare a b :=
    match compare a.rank b.rank with
    | Ordering.eq => compare a.suit b.suit
    | ord         => ord

-- ----------------------------------------
-- 10.3 カードを使ってみる
-- ----------------------------------------

-- カードの生成
def aceOfSpades  := Card.mk Suit.spade Rank.ace
def kingOfHearts := Card.mk Suit.heart Rank.king
def tenOfClubs   := Card.mk Suit.club Rank.ten
def aceOfHearts  := Card.mk Suit.heart Rank.ace

-- 表示
#eval toString aceOfSpades    -- "♠A"
#eval toString kingOfHearts   -- "♥K"
#eval toString tenOfClubs     -- "♣10"

-- 比較
#eval compare aceOfSpades kingOfHearts
-- => Ordering.gt  （A > K）

#eval compare tenOfClubs kingOfHearts
-- => Ordering.lt  （10 < K）

-- 同じランクならスートで比較
#eval compare aceOfSpades aceOfHearts
-- => Ordering.gt  （♠ > ♥）

-- 等値比較
#eval (aceOfSpades == aceOfSpades)   -- true
#eval (aceOfSpades == kingOfHearts)  -- false

-- ----------------------------------------
-- 10.4 カードの手札をソートする
-- ----------------------------------------

-- ポーカーの手札を用意
def hand : List Card := [
  Card.mk Suit.heart   Rank.king,
  Card.mk Suit.spade   Rank.three,
  Card.mk Suit.diamond Rank.ace,
  Card.mk Suit.club    Rank.seven,
  Card.mk Suit.heart   Rank.three
]

-- ランク順にソート（Ord インスタンスを利用）
def sortedHand : List Card :=
  hand.mergeSort (fun a b => compare a b != Ordering.gt)

-- 結果を表示
#eval hand.map toString
-- => ["♥K", "♠3", "♦A", "♣7", "♥3"]

#eval sortedHand.map toString
-- => ["♥3", "♠3", "♣7", "♥K", "♦A"]
-- ランク順に並び、同ランクならスート順

-- ----------------------------------------
-- 10.5 ジェネリック関数をカードに適用する
-- ----------------------------------------

-- 先ほど定義した maxOf がカードにも使える！
#eval toString (maxOf aceOfSpades kingOfHearts)
-- => "♠A"  （A > K なので♠A が返る）

-- 手札の最強カードを求める
-- listMax も使える（Ord と Inhabited が必要）
instance : Inhabited Card where
  default := Card.mk Suit.club Rank.two  -- 最弱のカードをデフォルトに

#eval toString (listMax hand)
-- => "♦A"  （手札の中で一番強いカード）

-- ----------------------------------------
-- 10.6 カードに関するユーティリティ関数
-- ----------------------------------------

-- 手札からスートでフィルタリング
def filterBySuit (cards : List Card) (s : Suit) : List Card :=
  cards.filter (fun c => c.suit == s)

#eval (filterBySuit hand Suit.heart).map toString
-- => ["♥K", "♥3"]

-- 手札にペア（同じランクのカードが2枚）があるかチェック
def hasPair [BEq α] [Ord α] (xs : List α) : Bool :=
  let sorted := xs.mergeSort (fun a b => compare a b != Ordering.gt)
  match sorted with
  | [] => false
  | _ :: rest =>
    -- ソート済みリストで隣接要素を比較
    (sorted.zip rest).any (fun (a, b) => a == b)

-- ランクだけ取り出してペアをチェック
def handRanks : List Nat := hand.map (fun c => c.rank.toNat)

#eval hasPair handRanks
-- => true  （3が2枚ある）


-- ============================================
-- まとめ
-- ============================================

-- 型クラスのポイント:
--
-- 1. class で「何ができるか」を宣言する
--    → Java の interface, Rust の trait に相当
--
-- 2. instance で「具体的にどうやるか」を実装する
--    → Java の implements, Rust の impl Trait for Type に相当
--
-- 3. [制約] でジェネリック関数に型クラスの要件を指定する
--    → Java の <T extends Interface>, Rust の fn foo<T: Trait> に相当
--
-- 4. deriving で機械的な実装を自動生成できる
--    → Rust の #[derive(...)] に相当
--
-- 5. 組み込み型クラス (ToString, BEq, Ord, ...) を実装すると、
--    Lean のエコシステム全体で自然に使える型になる

end Tutorial07
