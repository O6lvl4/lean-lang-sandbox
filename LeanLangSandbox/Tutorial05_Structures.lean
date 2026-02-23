-- ============================================
-- Tutorial 05: 構造体 (Structures)
-- 他言語のクラス / レコード / structに相当するもの
-- ============================================
-- Lean 4 の structure は、名前付きフィールドを持つ型を定義する仕組み。
-- TypeScript の interface + class、Rust の struct、Python の dataclass に近い。
-- ただし Lean の structure はイミュータブル（不変）。
-- 「変更」は常に新しいインスタンスの生成を意味する。

namespace Tutorial05

-- ============================================
-- 1. 基本的な構造体の定義
-- ============================================

-- 最もシンプルな構造体。2D の点を表す。
-- TypeScript でいうと:
--   interface Point2D { x: number; y: number }
-- Rust でいうと:
--   struct Point2D { x: f64, y: f64 }
structure Point2D where
  x : Float
  y : Float

-- deriving Repr を付けると #eval で中身を表示できる。
-- Repr は他言語の toString / Debug trait に相当。
-- deriving をつけ忘れると #eval でエラーになるので注意。
structure Point2DRepr where
  x : Float
  y : Float
deriving Repr

-- ============================================
-- 2. インスタンスの生成
-- ============================================

-- 方法1: { フィールド名 := 値 } 記法
-- これが最も基本的で明示的な書き方。
def origin : Point2DRepr := { x := 0.0, y := 0.0 }
def pointA : Point2DRepr := { x := 3.0, y := 4.0 }

-- #eval で確認（deriving Repr があるので表示できる）
#eval origin    -- { x := 0.000000, y := 0.000000 }
#eval pointA   -- { x := 3.000000, y := 4.000000 }

-- 方法2: 名前付きコンストラクタ Point2DRepr.mk
-- structure を定義すると、自動的に .mk コンストラクタが生成される。
def pointB : Point2DRepr := Point2DRepr.mk 1.0 2.0

#eval pointB   -- { x := 1.000000, y := 2.000000 }

-- 方法3: 匿名コンストラクタ ⟨...⟩ 記法
-- 型が推論できる場面で使える短縮記法。
-- ⟨ と ⟩ は VS Code で \langle と \rangle で入力。
-- コンストラクタが1つしかない型（structure は常にそう）で使える。
def pointC : Point2DRepr := ⟨5.0, 6.0⟩

#eval pointC   -- { x := 5.000000, y := 6.000000 }

-- ============================================
-- 3. フィールドアクセス（ドット記法）
-- ============================================
-- 他言語と同じく . でフィールドにアクセスできる。
-- これは実際には Point2DRepr.x という関数の呼び出し。

#eval pointA.x         -- 3.000000
#eval pointA.y         -- 4.000000

-- 関数としてのフィールドアクセサ
-- structure を定義すると、自動的に各フィールドの getter 関数が生成される。
-- Point2DRepr.x : Point2DRepr → Float
-- Point2DRepr.y : Point2DRepr → Float
#eval Point2DRepr.x pointA   -- 3.000000（ドット記法と同じ結果）

-- ============================================
-- 4. 構造体の更新（with 記法）
-- ============================================
-- Lean の structure はイミュータブルなので、「値を変える」のではなく
-- 「一部だけ変えた新しいインスタンスを作る」。
-- JavaScript の { ...obj, field: newValue } に似ている。
-- Rust の struct update syntax: Point { x: 10.0, ..point } にも似ている。

def pointD : Point2DRepr := { pointA with x := 10.0 }
-- pointA の y はそのまま、x だけ 10.0 に変えた新しいインスタンス

#eval pointD       -- { x := 10.000000, y := 4.000000 }
#eval pointA       -- { x := 3.000000, y := 4.000000 }（元は変わらない！）

-- 複数フィールドを同時に更新することもできる
def pointE : Point2DRepr := { origin with x := 7.0, y := 8.0 }

#eval pointE       -- { x := 7.000000, y := 8.000000 }

-- ============================================
-- 5. 構造体に対するメソッド定義
-- ============================================
-- Lean には class のメソッド定義構文はないが、
-- 「StructName.methodName」という名前空間に関数を定義すると
-- ドット記法で呼べるようになる。
-- これは Go の func (p Point) Distance() float64 に近い考え方。

-- 原点からの距離を計算するメソッド
def Point2DRepr.distanceFromOrigin (p : Point2DRepr) : Float :=
  (p.x * p.x + p.y * p.y).sqrt

-- ドット記法で呼べる！
#eval pointA.distanceFromOrigin   -- 5.000000（3-4-5 の直角三角形）

-- 2点間の距離
def Point2DRepr.distanceTo (p q : Point2DRepr) : Float :=
  ((p.x - q.x) * (p.x - q.x) + (p.y - q.y) * (p.y - q.y)).sqrt

#eval pointA.distanceTo pointB   -- 2.828427...（≒ √8）

-- 点を平行移動するメソッド（新しい点を返す）
def Point2DRepr.translate (p : Point2DRepr) (dx dy : Float) : Point2DRepr :=
  { p with x := p.x + dx, y := p.y + dy }

#eval pointA.translate 1.0 1.0   -- { x := 4.000000, y := 5.000000 }

-- 文字列変換メソッド
def Point2DRepr.toString (p : Point2DRepr) : String :=
  s!"({p.x}, {p.y})"

#eval pointA.toString   -- "(3.000000, 4.000000)"

-- ============================================
-- 6. deriving で自動導出できる型クラス
-- ============================================

-- Repr   : #eval で表示できるようにする（Debug 出力）
-- BEq    : == で比較できるようにする（構造的等価性）
-- Inhabited : デフォルト値を持つ型にする（default で取得可能）

structure Color where
  r : Nat
  g : Nat
  b : Nat
deriving Repr, BEq, Inhabited

-- BEq により == で比較可能
def red : Color := { r := 255, g := 0, b := 0 }
def green : Color := { r := 0, g := 255, b := 0 }
def blue : Color := { r := 0, g := 0, b := 255 }
def anotherRed : Color := { r := 255, g := 0, b := 0 }

#eval red == anotherRed   -- true（同じフィールド値なので等しい）
#eval red == green         -- false

-- Inhabited により default でデフォルト値を取得できる
-- Nat の default は 0 なので、全フィールドが 0 になる
#eval (default : Color)   -- { r := 0, g := 0, b := 0 }（黒になる）

-- Color のメソッド: 16進数文字列に変換
def Color.toHex (c : Color) : String :=
  let toHex2 (n : Nat) : String :=
    let hi := n / 16
    let lo := n % 16
    let hexChar (d : Nat) : String :=
      if d < 10 then toString d
      else if d == 10 then "A"
      else if d == 11 then "B"
      else if d == 12 then "C"
      else if d == 13 then "D"
      else if d == 14 then "E"
      else "F"
    hexChar hi ++ hexChar lo
  s!"#{toHex2 c.r}{toHex2 c.g}{toHex2 c.b}"

#eval red.toHex     -- "#FF0000"
#eval green.toHex   -- "#00FF00"
#eval blue.toHex    -- "#0000FF"

-- 色の混合（単純平均）
def Color.mix (c1 c2 : Color) : Color :=
  { r := (c1.r + c2.r) / 2
  , g := (c1.g + c2.g) / 2
  , b := (c1.b + c2.b) / 2
  }

#eval (Color.mix red green).toHex   -- "#7F7F00"（黄色っぽい）

-- ============================================
-- 7. ネストされた構造体
-- ============================================
-- 構造体のフィールドに別の構造体を使える。
-- 他言語のオブジェクト合成 / コンポジションと同じ。

structure Person where
  name : String
  age  : Nat
deriving Repr, BEq

structure Address where
  city     : String
  zipCode  : String
deriving Repr

structure Employee where
  person  : Person
  address : Address
  salary  : Nat
deriving Repr

def alice : Employee :=
  { person  := { name := "Alice", age := 30 }
  , address := { city := "Tokyo", zipCode := "100-0001" }
  , salary  := 5000000
  }

-- ネストされたフィールドへのアクセス
#eval alice.person.name       -- "Alice"
#eval alice.person.age        -- 30
#eval alice.address.city      -- "Tokyo"
#eval alice.salary            -- 5000000

-- ネストされた構造体の更新
-- 残念ながら alice.person.age := 31 のような深いネスト更新はできない。
-- 手動でネスト部分を更新する必要がある。
def aliceNextYear : Employee :=
  { alice with person := { alice.person with age := 31 } }

#eval aliceNextYear.person.age   -- 31

-- ============================================
-- 8. デフォルト値付きの構造体
-- ============================================
-- フィールドにデフォルト値を指定できる。
-- インスタンス生成時に省略したフィールドはデフォルト値が使われる。
-- Python の dataclass(default=...) や Kotlin の data class のデフォルト引数に近い。

structure Config where
  host    : String := "localhost"
  port    : Nat    := 8080
  debug   : Bool   := false
  maxConn : Nat    := 100
deriving Repr

-- 全部デフォルトで作成
def defaultConfig : Config := {}

#eval defaultConfig   -- { host := "localhost", port := 8080, debug := false, maxConn := 100 }

-- 一部だけ上書き
def devConfig : Config := { debug := true, port := 3000 }

#eval devConfig   -- { host := "localhost", port := 3000, debug := true, maxConn := 100 }

-- 本番用設定
def prodConfig : Config :=
  { host := "api.example.com"
  , port := 443
  , maxConn := 10000
  }

#eval prodConfig   -- { host := "api.example.com", port := 443, debug := false, maxConn := 10000 }

-- ============================================
-- 9. 実践例: 銀行口座（BankAccount）
-- ============================================
-- イミュータブルな銀行口座をモデリングする。
-- 全ての操作は新しい BankAccount を返す（元の値は変わらない）。

structure BankAccount where
  owner   : String
  balance : Int     -- 整数（マイナスもありえる概念として Int を使用）
  frozen  : Bool := false
deriving Repr

-- 口座を作成
def BankAccount.create (owner : String) (initialDeposit : Int) : BankAccount :=
  { owner := owner, balance := initialDeposit }

-- 入金（凍結中は不可）
def BankAccount.deposit (acc : BankAccount) (amount : Int) : BankAccount :=
  if acc.frozen then acc
  else { acc with balance := acc.balance + amount }

-- 出金（凍結中 or 残高不足は不可）
def BankAccount.withdraw (acc : BankAccount) (amount : Int) : BankAccount :=
  if acc.frozen then acc
  else if acc.balance < amount then acc
  else { acc with balance := acc.balance - amount }

-- 口座凍結
def BankAccount.freeze (acc : BankAccount) : BankAccount :=
  { acc with frozen := true }

-- 口座凍結解除
def BankAccount.unfreeze (acc : BankAccount) : BankAccount :=
  { acc with frozen := false }

-- 残高表示
def BankAccount.summary (acc : BankAccount) : String :=
  let status := if acc.frozen then " [凍結中]" else ""
  s!"{acc.owner}: {acc.balance} 円{status}"

-- 使ってみる
def myAccount : BankAccount := BankAccount.create "Taro" 100000

#eval myAccount.summary
  -- "Taro: 100000 円"

#eval (myAccount.deposit 50000).summary
  -- "Taro: 150000 円"

#eval (myAccount.deposit 50000 |>.withdraw 30000).summary
  -- "Taro: 120000 円"
  -- |> はパイプ演算子。前の結果を次の関数の第1引数に渡す。
  -- Unix の | や F# の |> と同じ。

-- 凍結した口座からは出金できない
def frozenAccount := myAccount.freeze

#eval frozenAccount.summary
  -- "Taro: 100000 円 [凍結中]"

#eval (frozenAccount.withdraw 50000).summary
  -- "Taro: 100000 円 [凍結中]"（凍結中なので残高変わらず）

#eval (frozenAccount.unfreeze.withdraw 50000).summary
  -- "Taro: 50000 円"（解凍してから出金）

-- メソッドチェーンの例
-- ドット記法のおかげで、OOP風に書ける
#eval (BankAccount.create "Hanako" 200000
  |>.deposit 30000
  |>.withdraw 10000
  |>.deposit 5000).summary
  -- "Hanako: 225000 円"

-- ============================================
-- 10. ジェネリックな構造体（型パラメータ付き）
-- ============================================
-- 他言語のジェネリクス / テンプレートに相当。
-- TypeScript でいう interface Pair<A, B> { fst: A; snd: B }

structure Pair (α β : Type) where
  fst : α
  snd : β
deriving Repr

def intStringPair : Pair Nat String := ⟨42, "hello"⟩
def boolPair : Pair Bool Bool := { fst := true, snd := false }

#eval intStringPair       -- { fst := 42, snd := "hello" }
#eval intStringPair.fst   -- 42
#eval intStringPair.snd   -- "hello"
#eval boolPair             -- { fst := true, snd := false }

-- ジェネリックなメソッド
def Pair.swap (p : Pair α β) : Pair β α :=
  ⟨p.snd, p.fst⟩

#eval intStringPair.swap   -- { fst := "hello", snd := 42 }

-- ============================================
-- 11. 構造体と名前空間（namespace）
-- ============================================
-- structure Foo を定義すると、自動的に namespace Foo が作られる。
-- その中に関数を定義すると、ドット記法で呼べる。
-- 明示的に namespace を開いて書くこともできる。

structure Rectangle where
  width  : Float
  height : Float
deriving Repr

namespace Rectangle

-- namespace の中で定義すれば、Rectangle. を省略できる
def area (r : Rectangle) : Float :=
  r.width * r.height

def perimeter (r : Rectangle) : Float :=
  2.0 * (r.width + r.height)

def isSquare (r : Rectangle) : Bool :=
  r.width == r.height

def scale (r : Rectangle) (factor : Float) : Rectangle :=
  { width := r.width * factor, height := r.height * factor }

def toString (r : Rectangle) : String :=
  s!"{r.width} x {r.height} (area: {r.area})"

end Rectangle

def myRect : Rectangle := { width := 10.0, height := 5.0 }

#eval myRect.area        -- 50.000000
#eval myRect.perimeter   -- 30.000000
#eval myRect.isSquare    -- false
#eval myRect.scale 2.0   -- { width := 20.000000, height := 10.000000 }
#eval myRect.toString    -- "10.000000 x 5.000000 (area: 50.000000)"

def square : Rectangle := { width := 4.0, height := 4.0 }
#eval square.isSquare    -- true

-- ============================================
-- 12. まとめ
-- ============================================
-- structure は Lean 4 におけるデータ構造の基本。
--
-- 覚えておくべきこと:
-- 1. structure は不変（イミュータブル）。更新は新しいインスタンスの生成。
-- 2. { field := value } で生成、 ⟨val1, val2⟩ で短縮生成。
-- 3. { obj with field := newValue } で部分更新。
-- 4. StructName.methodName で定義すればドット記法で呼べる。
-- 5. deriving Repr, BEq, Inhabited で便利な機能を自動導出。
-- 6. デフォルト値を設定できる（field : Type := defaultValue）。
-- 7. 型パラメータを使えばジェネリックな構造体も作れる。
--
-- 他言語との対応:
-- | Lean 4          | TypeScript       | Rust              | Python          |
-- |-----------------|------------------|-------------------|-----------------|
-- | structure       | interface + class| struct            | @dataclass      |
-- | { f := v }      | { f: v }         | Foo { f: v }      | Foo(f=v)        |
-- | { o with f := } | { ...o, f: v }   | Foo { f: v, ..o } | replace(f=v)    |
-- | deriving Repr   | toString()       | #[derive(Debug)]  | __repr__        |
-- | deriving BEq    | 手動実装         | #[derive(PartialEq)]| __eq__        |
-- | .methodName     | obj.method()     | impl Foo { fn }   | def method(self)|

end Tutorial05
