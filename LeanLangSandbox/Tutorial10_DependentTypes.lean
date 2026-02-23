-- ============================================
-- Tutorial 10: 依存型 (Dependent Types)
-- 「型が値に依存する」という革命的な概念
-- ============================================
--
-- 他の言語を知っている開発者向け:
--
--   TypeScript: number[], string[] ... 型は「要素の型」だけを知っている
--   Python:     list[int]          ... 同上
--   Lean 4:     Vect 3 Nat         ... 「長さが3のNatのリスト」まで型に入る！
--
-- 依存型とは「型が値によって決まる」仕組み。
-- これにより、従来は実行時にしか検出できなかったバグを
-- コンパイル時に完全に排除できる。
--
-- この章は高度だが、依存型の威力を実感できる最もエキサイティングな章。

namespace Tutorial10

-- ============================================
-- 第1節: 依存型とは何か？
-- ============================================
--
-- 通常の型:
--   List Nat      -- 「Natのリスト」（長さは不明）
--   Array String  -- 「Stringの配列」（長さは不明）
--
-- 依存型:
--   Vect n Nat    -- 「長さが n のNatのリスト」（n は値！）
--   Fin n         -- 「0以上 n未満 の自然数」（n は値！）
--
-- ポイント: 型の中に「値」が現れている。
-- つまり「型が値に依存している」= 依存型 (Dependent Type)
--
-- TypeScript の世界で考えると:
--   type Vect<N extends number, T> = ???
--   // TypeScript ではこれを正確に表現できない！
--   // タプル [T, T, T] は書けるが、N を変数にできない
--
-- Python の世界で考えると:
--   Vector[3, int]  # こんな型は存在しない
--   # 長さチェックは全て実行時に assert で行う

-- ============================================
-- 第2節: Vect - 長さ付きリスト
-- ============================================

-- Vect n α: 長さが正確に n であることが「型で保証」されたリスト
-- n : Nat は長さ、α は要素の型
--
-- 技術的なポイント:
--   Lean 4 の Nat.add は第2引数で再帰する。
--   つまり n + 0 = n は定義から成り立つが、0 + n = n は帰納法が必要。
--   この「定義的等しさ」(definitional equality) を意識して設計する必要がある。
--   Lean 4 で Vect を扱う際、型レベルの算術が「定義的に」合わないことがある。
--   そのような場合は ▸ (rewrite) や omega タクティクで型を合わせる。
--   これは依存型プログラミングの「現実」であり、知っておくべき重要な点。
inductive Vect (α : Type) : Nat → Type where
  -- 空のベクタ: 長さは 0
  | nil  : Vect α 0
  -- 先頭に要素を追加: 長さが n なら n+1 になる
  | cons : α → Vect α n → Vect α (n + 1)
  deriving Repr

namespace Vect

-- ----------------------------------------
-- 2.1 head: 絶対に失敗しない先頭要素の取得
-- ----------------------------------------
--
-- 【他の言語との比較】
--
-- TypeScript:
--   function head<T>(arr: T[]): T {
--     if (arr.length === 0) throw new Error("empty array!");  // 実行時エラー
--     return arr[0];
--   }
--
-- Python:
--   def head(lst: list) -> Any:
--     if not lst: raise IndexError("empty list")  # 実行時エラー
--     return lst[0]
--
-- Lean (List版 - Option が必要):
--   def head? : List α → Option α  -- None が返る可能性がある
--
-- Lean (Vect版 - 依存型の威力！):
--   空リストを渡すことが「型レベルで不可能」なので、失敗しない！
def head : Vect α (n + 1) → α
  -- 引数の型が Vect α (n + 1) なので、n + 1 >= 1 が保証される
  -- つまり Vect.nil (長さ0) を渡すことはコンパイルエラーになる！
  | .cons x _ => x

-- 動作確認
#eval Vect.head (.cons 42 (.cons 99 .nil))  -- 42

-- 以下はコンパイルエラーになる（試してみよう！コメントを外すとエラー）:
-- #eval Vect.head Vect.nil
-- エラー: Vect.nil は Vect 0 α 型だが、Vect (n + 1) α が必要

-- ----------------------------------------
-- 2.2 tail: 先頭を除いた残り（これも安全）
-- ----------------------------------------
def tail : Vect α (n + 1) → Vect α n
  | .cons _ xs => xs

#eval Vect.tail (.cons 1 (.cons 2 (.cons 3 .nil)))
-- Vect.cons 2 (Vect.cons 3 (Vect.nil))

-- ----------------------------------------
-- 2.3 map: 各要素に関数を適用
-- ----------------------------------------
--
-- 注目: 入力が Vect n α なら出力も Vect n β
-- 長さが変わらないことが型で保証されている！
--
-- TypeScript では:
--   arr.map(f)  // 長さが同じかどうかは信じるしかない
--
-- Lean の Vect では:
--   map f v     // 戻り値の型が Vect n β なので、長さ不変が証明済み
def map (f : α → β) : Vect α n → Vect β n
  | .nil       => .nil                    -- 空なら空 (0 → 0)
  | .cons x xs => .cons (f x) (map f xs)  -- 先頭を変換して再帰 (n+1 → n+1)

#eval Vect.map (· * 10) (.cons 1 (.cons 2 (.cons 3 .nil)))
-- Vect.cons 10 (Vect.cons 20 (Vect.cons 30 (Vect.nil)))

-- ----------------------------------------
-- 2.4 append: 2つのベクタを結合
-- ----------------------------------------
--
-- 最も感動的な部分:
--   Vect n α と Vect m α を結合すると Vect (n + m) α になる
--   この「n + m」が型レベルで正確に計算される！
--
-- TypeScript:
--   function append<T>(a: T[], b: T[]): T[] { return [...a, ...b]; }
--   // 結果の長さが a.length + b.length であることは祈るしかない
--
-- Lean:
--   append : Vect n α → Vect m α → Vect (n + m) α
--   // 結果の長さが n + m であることがコンパイル時に証明される！
--
-- 【依存型の現実】
-- Lean 4 の + (Nat.add) は第2引数で再帰定義されている:
--   n + 0     = n       (定義的に成立)
--   n + (m+1) = (n+m)+1 (定義的に成立)
-- しかし:
--   0 + m     = m       (定義的には成立しない！帰納法が必要)
--   (n+1) + m = (n+m)+1 (定義的には成立しない！)
--
-- そのため、型レベルの等式を合わせる必要がある。
-- ここではタクティクモードを使い、omega で算術の等式を自動証明する。
-- これは依存型プログラミングの「現実」であり、避けて通れない重要な概念。
def append : Vect α n → Vect α m → Vect α (n + m)
  | .nil,       ys => by
    -- ys は Vect m α だが、戻り値は Vect (0 + m) α が必要
    -- 0 + m = m は定義的には成り立たないので、rw で型を書き換える
    -- rw はゴール内の式を等式で置き換えるタクティク
    rw [Nat.zero_add]
    exact ys
  | .cons x xs, ys => by
    -- .cons x (append xs ys) は Vect ((k+m)+1) α 型 (k は xs の長さ)
    -- しかし戻り値の型は Vect ((k+1) + m) α
    -- Nat.succ_add で (k+1) + m = (k+m) + 1 と書き換えて型を合わせる
    rw [Nat.succ_add]
    exact .cons x (append xs ys)

-- 使用例: 長さ2 + 長さ3 = 長さ5 が型で保証
def v2 : Vect Nat 2 := .cons 1 (.cons 2 .nil)
def v3 : Vect Nat 3 := .cons 3 (.cons 4 (.cons 5 .nil))
def v5 : Vect Nat 5 := append v2 v3
-- ↑ 型が Vect (2+3) Nat = Vect 5 Nat と自動的に計算される

#eval v5
-- Vect.cons 1 (Vect.cons 2 (Vect.cons 3 (Vect.cons 4 (Vect.cons 5 (Vect.nil)))))

-- ----------------------------------------
-- 2.5 replicate: 同じ値を n 個並べる
-- ----------------------------------------
-- 返り値の長さが引数 n と一致することが型で保証される
def replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0     => .nil
  | k + 1 => .cons x (replicate k x)

#eval Vect.replicate 4 "hello"
-- Vect.cons "hello" (Vect.cons "hello" (Vect.cons "hello" (Vect.cons "hello" (Vect.nil))))

-- ----------------------------------------
-- 2.6 zip: 同じ長さの2つのベクタを組にする
-- ----------------------------------------
-- 両方とも Vect n なので、長さが合わない心配が一切ない！
--
-- TypeScript:
--   function zip<A, B>(a: A[], b: B[]): [A, B][] {
--     return a.map((x, i) => [x, b[i]]);  // b が短いと undefined に！
--   }
--
-- Lean:
--   両方が Vect n 型なので、長さ不一致は型エラー。実行時エラーにならない。
def zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil,       .nil       => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

#eval Vect.zip (.cons 1 (.cons 2 .nil)) (.cons "a" (.cons "b" .nil))
-- Vect.cons (1, "a") (Vect.cons (2, "b") (Vect.nil))

-- ----------------------------------------
-- 2.7 安全なインデックスアクセス (Fin を使用)
-- ----------------------------------------
--
-- 【他の言語との比較】
--
-- TypeScript:
--   const arr = [10, 20, 30];
--   arr[5];  // undefined (実行時に静かにバグを生む)
--
-- Python:
--   arr = [10, 20, 30]
--   arr[5]   # IndexError: list index out of range (実行時例外)
--
-- Lean (Vect + Fin):
--   Vect.get v (5 : Fin 3)  -- コンパイルエラー！ 5 は Fin 3 に入らない
--   インデックスが範囲外であることがコンパイル時に検出される。

-- Vect (n+1) α から Fin (n+1) でアクセス: 絶対に範囲外にならない
-- Fin (n+1) は 0 以上 n+1 未満の数なので、Vect (n+1) のインデックスとしてぴったり
def get : Vect α n → Fin n → α
  | .cons x _,  ⟨0,     _⟩  => x
  | .cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, by omega⟩

-- 使用例
def sampleVec : Vect String 3 := .cons "zero" (.cons "one" (.cons "two" .nil))

#eval sampleVec.get ⟨0, by omega⟩  -- "zero"
#eval sampleVec.get ⟨1, by omega⟩  -- "one"
#eval sampleVec.get ⟨2, by omega⟩  -- "two"

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- #eval sampleVec.get ⟨3, by omega⟩
-- エラー: omega で 3 < 3 を証明できない（当然！）

end Vect

-- ============================================
-- 第3節: Fin n - 範囲が保証された自然数
-- ============================================
--
-- Fin n は「0 以上 n 未満の自然数」を表す型。
-- 配列の添字として使えば、範囲外アクセスが型レベルで不可能になる！
--
-- Lean 4 には Fin が標準で定義されている:
--   structure Fin (n : Nat) where
--     val : Nat
--     isLt : val < n
--
-- val が実際の値、isLt が「val < n」の証明。
-- つまり Fin 5 を作るには「0〜4のどれかの値」と「それが5未満である証明」が必要。

-- ----------------------------------------
-- 3.1 Fin の基本的な使い方
-- ----------------------------------------

-- Fin 5 は 0, 1, 2, 3, 4 のいずれか
def myFin : Fin 5 := ⟨3, by omega⟩  -- 3 < 5 の証明は omega が自動解決

-- リテラルからも作れる（Lean が自動的に範囲チェック）
def myFin2 : Fin 5 := 2  -- OK: 2 < 5
def myFin3 : Fin 5 := 4  -- OK: 4 < 5

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- def badFin : Fin 5 := 5   -- エラー！ 5 < 5 は偽
-- def badFin2 : Fin 5 := 10 -- エラー！ 10 < 5 は偽

-- ----------------------------------------
-- 3.2 Fin を使った安全な配列アクセス
-- ----------------------------------------
-- Lean 4 の標準 Array にも Fin を使った安全なアクセスがある

-- 配列を定義
def myArray : Array String := #["apple", "banana", "cherry"]

-- Array.get は Fin を使って安全にアクセスする
-- myArray.size = 3 なので、Fin 3 = {0, 1, 2} でアクセスできる
#eval myArray[0]  -- "apple"
#eval myArray[1]  -- "banana"
#eval myArray[2]  -- "cherry"

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- #eval myArray.get ⟨3, by omega⟩  -- エラー！ 3 < 3 の証明ができない

-- ----------------------------------------
-- 3.3 Fin の算術: 範囲内に収まることが保証される
-- ----------------------------------------

-- Fin 同士の比較
def compareFins : Bool :=
  let a : Fin 10 := 3
  let b : Fin 10 := 7
  a < b  -- true (3 < 7)

#eval compareFins  -- true

-- Fin の値を取り出す
#eval (myFin : Fin 5).val  -- 3

-- ============================================
-- 第4節: Subtype（部分型）- 条件付きの値
-- ============================================
--
-- Subtype は「ある条件を満たす値」を型として表現する。
-- Lean では { x : α // P x } という記法で書ける。
--
-- 例: { x : Nat // x > 0 }  -- 「0より大きい自然数」の型
--
-- これは構造体で言えば:
--   structure Subtype (P : α → Prop) where
--     val : α          -- 実際の値
--     property : P val -- 条件を満たす証明
--
-- 値と「その値が条件を満たす証明」をペアにして持つ。
-- 証明は実行時にはコストゼロ（消去される）。

-- ----------------------------------------
-- 4.1 正の自然数 (Positive Natural Number)
-- ----------------------------------------

-- PositiveNat: 0より大きいことが型で保証された自然数
abbrev PositiveNat := { n : Nat // n > 0 }

-- PositiveNat を作るには値と証明の両方が必要
def posThree : PositiveNat := ⟨3, by omega⟩     -- OK: 3 > 0
def posHundred : PositiveNat := ⟨100, by omega⟩  -- OK: 100 > 0

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- def posOops : PositiveNat := ⟨0, by omega⟩   -- エラー！ 0 > 0 は偽

-- ----------------------------------------
-- 4.2 安全な割り算
-- ----------------------------------------
--
-- 通常の割り算: ゼロ除算の危険がある
--   TypeScript: 1 / 0  → Infinity (静かにバグを生む)
--   Python:     1 / 0  → ZeroDivisionError (実行時例外)
--
-- 依存型を使えば: 除数が0でないことをコンパイル時に保証できる

-- 除数が正であることが型で保証された安全な割り算
def safeDiv (a : Nat) (b : PositiveNat) : Nat :=
  a / b.val

#eval safeDiv 10 ⟨3, by omega⟩   -- 3
#eval safeDiv 100 ⟨7, by omega⟩  -- 14

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- #eval safeDiv 10 ⟨0, by omega⟩  -- 0 > 0 の証明が作れない！

-- ----------------------------------------
-- 4.3 非空リスト
-- ----------------------------------------

-- 「空でないリスト」を型で表現
abbrev NonEmptyList (α : Type) := { xs : List α // xs ≠ [] }

-- 安全な head: Option 不要、例外も不要
-- リストが空でないことが型で保証されているので、先頭要素は必ず存在する
-- nel.val がリストの値、nel.property が「空でない」の証明
-- [] のケースは nel.property ([] ≠ [] の証明) が矛盾するため、
-- Lean が自動的に不可能と判定する
def neHead (nel : NonEmptyList α) : α :=
  match nel.val, nel.property with
  | x :: _, _ => x

-- 使用例
def myNEL : NonEmptyList Nat := ⟨[1, 2, 3], by decide⟩
#eval neHead myNEL  -- 1

-- 空リストは渡せない（コメントを外すとエラー）:
-- def emptyNEL : NonEmptyList Nat := ⟨[], by decide⟩
-- エラー: [] != [] の証明ができない（当然！）

-- ----------------------------------------
-- 4.4 偶数型
-- ----------------------------------------

-- 偶数であることが保証された自然数
abbrev EvenNat := { n : Nat // n % 2 = 0 }

def evenFour : EvenNat := ⟨4, by decide⟩
def evenZero : EvenNat := ⟨0, by decide⟩

-- 奇数は作れない:
-- def evenFive : EvenNat := ⟨5, by decide⟩  -- エラー！ 5 % 2 = 0 は偽

-- 偶数同士の足し算は偶数（これも証明できる！）
def addEven (a b : EvenNat) : EvenNat :=
  ⟨a.val + b.val, by omega⟩

#eval (addEven evenFour ⟨6, by decide⟩).val  -- 10

-- ============================================
-- 第5節: 依存型がバグを防ぐ実践例
-- ============================================

-- ----------------------------------------
-- 5.1 行列の型安全な表現
-- ----------------------------------------
--
-- 行列の掛け算: (m x n) 行列 x (n x p) 行列 = (m x p) 行列
-- 内側の次元 n が一致しないと掛け算できない。
--
-- TypeScript:
--   function matMul(a: number[][], b: number[][]): number[][] {
--     // a の列数と b の行数が一致するかは実行時チェック...
--     if (a[0].length !== b.length) throw new Error("dimension mismatch");
--     ...
--   }
--
-- Lean (依存型):
--   型シグネチャだけで次元の一致が保証される

-- 行列を「行のベクタのベクタ」として定義
-- Matrix m n α = m行 n列 の行列
abbrev Matrix (m n : Nat) (α : Type) := Vect (Vect α n) m

-- 行列の具体例: 2行3列のNat行列
def exampleMatrix : Matrix 2 3 Nat :=
  .cons (.cons 1 (.cons 2 (.cons 3 .nil)))
  (.cons (.cons 4 (.cons 5 (.cons 6 .nil)))
  .nil)

-- Matrix 2 3 Nat は「2行3列のNat行列」
-- 型だけで行列のサイズが確定している！
-- 行の長さが不揃いなデータは型エラーで作れない:
-- 以下はコンパイルエラー:
-- def badMatrix : Matrix 2 3 Nat :=
--   .cons (.cons 1 (.cons 2 .nil))  -- 長さ2 != 3 でエラー！
--   (.cons (.cons 4 (.cons 5 (.cons 6 .nil)))
--   .nil)

-- ----------------------------------------
-- 5.2 型安全なステートマシン
-- ----------------------------------------
--
-- ドアの状態を型で管理する例
-- 「閉まっているドアしか開けられない」
-- 「開いているドアしか閉められない」を型で強制する
--
-- TypeScript では:
--   class Door {
--     state: "open" | "closed";
--     open() {
--       if (this.state !== "closed") throw new Error("already open!");
--       this.state = "open";
--     }
--   }
--   // 実行時にしかエラーを検出できない
--
-- Lean (依存型):
--   不正な状態遷移はコンパイルエラーになる

inductive DoorState where
  | opened
  | closed
  deriving Repr

-- Door は状態をパラメータに持つ（依存型！）
inductive Door : DoorState → Type where
  | mk : (label : String) → Door s
  deriving Repr

-- 閉じたドアだけを開けられる
def openDoor : Door DoorState.closed → Door DoorState.opened
  | Door.mk label => Door.mk label

-- 開いたドアだけを閉じられる
def closeDoor : Door DoorState.opened → Door DoorState.closed
  | Door.mk label => Door.mk label

-- 使用例
def myDoor : Door DoorState.closed := Door.mk "正面玄関"
def openedDoor := openDoor myDoor      -- OK: 閉じたドアを開ける
def closedAgain := closeDoor openedDoor -- OK: 開いたドアを閉じる

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- def bad1 := openDoor openedDoor     -- エラー！ 開いたドアは開けられない
-- def bad2 := closeDoor myDoor        -- エラー！ 閉じたドアは閉じられない

-- ----------------------------------------
-- 5.3 型安全なプロトコル: ソケットの状態管理
-- ----------------------------------------
--
-- ネットワークプログラミングでありがちなバグ:
--   - 接続前に送信してしまう
--   - 切断後に読み取ろうとする
--
-- 依存型を使えば、正しい順序でしか操作を呼べない

inductive SocketState where
  | created
  | connected
  | closed
  deriving Repr

-- ソケットの型（状態がパラメータ）
structure Socket (s : SocketState) where
  host : String
  port : Nat
  deriving Repr

-- 作成 → 接続
def connectSocket : Socket SocketState.created → Socket SocketState.connected
  | ⟨host, port⟩ => ⟨host, port⟩

-- 接続中 → 切断
def closeSocket : Socket SocketState.connected → Socket SocketState.closed
  | ⟨host, port⟩ => ⟨host, port⟩

-- 送信は接続中のソケットのみ
def sendData (_data : String) : Socket SocketState.connected → Socket SocketState.connected
  | s => s

-- 使用例: 正しい順序
def socketDemo :=
  let sock : Socket SocketState.created := ⟨"example.com", 80⟩
  let connected := connectSocket sock
  let connected := sendData "Hello" connected
  let _closed := closeSocket connected
  "done"

-- 以下はコンパイルエラー（コメントを外すとエラー）:
-- def socketBad :=
--   let sock : Socket SocketState.created := ⟨"example.com", 80⟩
--   sendData "Hello" sock  -- エラー！ 未接続のソケットには送信できない

-- ============================================
-- 第6節: 依存型で証明する
-- ============================================

-- ----------------------------------------
-- 6.1 Vect の性質: 型シグネチャそのものが証明
-- ----------------------------------------
--
-- Vect.append の型シグネチャ:
--   append : Vect n α → Vect m α → Vect (n + m) α
--
-- この型が通るということは:
-- 「長さ n のベクタと長さ m のベクタを結合すると
--  長さ n + m のベクタになる」
-- という命題が証明されたことを意味する。
--
-- Vect.map の型シグネチャ:
--   map : (α → β) → Vect n α → Vect n β
-- 入力も出力も同じ n → 長さが変わらないことが型で自明。
--
-- Vect.zip の型シグネチャ:
--   zip : Vect n α → Vect n β → Vect n (α × β)
-- 両方の入力と出力が全て同じ n → 長さの一致が型で保証。

-- ----------------------------------------
-- 6.2 具体的な値での証明
-- ----------------------------------------

-- head は最初の要素を返すことの証明
example : Vect.head (.cons 42 (.cons 99 .nil)) = 42 := by rfl

-- replicate は指定した値で埋めることの証明
example : Vect.replicate 3 "x" = .cons "x" (.cons "x" (.cons "x" .nil)) := by rfl

-- map は各要素に関数を適用することの証明
example : Vect.map (· + 1) (.cons 10 (.cons 20 .nil))
        = .cons 11 (.cons 21 .nil) := by rfl

-- ============================================
-- 第7節: まとめ - 他の言語との比較表
-- ============================================
--
-- +------------------+--------------+-------------+----------------------+
-- | 操作             | TypeScript   | Python      | Lean 4 (依存型)      |
-- +------------------+--------------+-------------+----------------------+
-- | 空リストの head  | undefined    | IndexError  | コンパイルエラー     |
-- | 配列の範囲外参照 | undefined    | IndexError  | コンパイルエラー     |
-- | ゼロ除算         | Infinity     | ZeroDivError| コンパイルエラー     |
-- | リスト結合の長さ | 信じるだけ   | 信じるだけ  | 型で証明済み         |
-- | 行列次元の不一致 | 実行時エラー | 実行時エラー| コンパイルエラー     |
-- | 不正な状態遷移   | 実行時エラー | 実行時エラー| コンパイルエラー     |
-- +------------------+--------------+-------------+----------------------+
--
-- 依存型のメリット:
-- 1. バグがコンパイル時に見つかる → デバッグ時間が激減
-- 2. テストでは見つけられない種類のバグも防げる
--    (テストは有限個のケースしか検証できないが、型は全てのケースをカバー)
-- 3. 型がドキュメントになる → コードの意図が型シグネチャから読み取れる
-- 4. リファクタリングが安全 → 型が壊れたらコンパイラが教えてくれる
--
-- 依存型のデメリット:
-- 1. 学習コストが高い（この章を読んでいるあなたは乗り越えつつある！）
-- 2. 型レベルの算術で定義的等しさの問題に遭遇することがある
--    (append で rw を使ったように、型を手動で合わせる必要がある場合がある)
-- 3. 証明が必要になることがある（omega, simp, decide, rfl などが助けてくれる）
-- 4. 型が複雑になりすぎると読みにくくなることもある
--
-- 結論:
-- 依存型は「正しさをコンパイラに保証させる」最強の仕組み。
-- 全てのコードに使う必要はないが、重要な不変条件（長さ、範囲、
-- 非空、正値など）を型で表現できると、バグのないソフトウェアに
-- 大きく近づける。
--
-- 特に以下のパターンが実用的:
--   - Fin n を使った安全なインデックスアクセス
--   - Subtype ({ x // P x }) を使った値の制約（正数、非空など）
--   - 状態パラメータを使ったプロトコルの強制（Door, Socket の例）
--   - Vect のような長さ付きデータ構造

end Tutorial10
