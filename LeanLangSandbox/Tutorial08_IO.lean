-- ============================================
-- Tutorial 08: IO モナド入門
-- 「純粋関数型言語で副作用を扱う仕組み」
-- ============================================
-- 他言語経験者向け: Lean 4 は純粋関数型言語だが、
-- IO モナドを使うことで、コンソール入出力・ファイル操作・
-- 可変変数など「副作用のある処理」を安全に記述できる。
--
-- TypeScript/Python 等の命令型言語に慣れた人には
-- 「do ブロックの中は普通の命令型プログラミングっぽく書ける」
-- と理解するのが最初の一歩。

namespace Tutorial08

-- ============================================
-- 1. IO モナドの基本: IO とは何か
-- ============================================
-- IO α は「実行すると副作用を起こし、α 型の値を返すアクション」
--
-- 他言語との対比:
--   TypeScript: Promise<T> に近い（実行を遅延し、結果を返す）
--   Rust:       Future<T> にも似ている
--   Haskell:    IO a そのもの
--
-- よく使う型:
--   IO Unit   -- 戻り値なし（void に相当）。println 等
--   IO String -- 文字列を返す IO アクション。ユーザー入力等
--   IO Nat    -- 自然数を返す IO アクション
--   IO Bool   -- 真偽値を返す IO アクション

-- ============================================
-- 2. 最もシンプルな IO: IO.println と IO.print
-- ============================================

-- IO.println : String → IO Unit
--   改行付きで文字列を出力する（puts, console.log に相当）
-- IO.print : String → IO Unit
--   改行なしで文字列を出力する（process.stdout.write に相当）

-- #eval で IO アクションを実行できる（REPL的に確認可能）
#eval IO.println "Hello, Lean 4!"
-- 出力: Hello, Lean 4!

#eval IO.print "改行なし"
-- 出力: 改行なし（改行されない）

-- ============================================
-- 3. do 記法（do notation）
-- ============================================
-- 複数の IO アクションを順番に実行するための構文糖衣。
-- 他言語の「ブロック（{ ... }）」に相当する。
-- do の中では、命令型言語のように上から下へ順に実行される。

#eval do
  IO.println "1行目"
  IO.println "2行目"
  IO.println "3行目"
-- 出力:
-- 1行目
-- 2行目
-- 3行目

-- do ブロックは関数定義の中でも使える
def greet : IO Unit := do
  IO.println "こんにちは！"
  IO.println "Lean 4 の世界へようこそ"

#eval greet
-- 出力:
-- こんにちは！
-- Lean 4 の世界へようこそ

-- ============================================
-- 4. let による束縛（immutable な変数）
-- ============================================
-- do ブロック内で let を使うと、値を変数に束縛できる。
-- IO アクションの結果を受け取るには ← を使う。

-- 4.1 純粋な値の束縛（← 不要）
#eval do
  let name := "太郎"          -- 純粋な値の束縛。IO アクションではないので ← は不要
  let age := 25
  IO.println s!"名前: {name}, 年齢: {age}"
-- 出力: 名前: 太郎, 年齢: 25

-- 4.2 IO アクションの結果を束縛（← が必要）
-- ← は IO アクションを「実行」して、中の値を取り出す演算子。
-- TypeScript の await に非常に近い概念。
--   let x ← someIOAction   -- someIOAction を実行し、結果を x に束縛
--   let x := pureValue      -- 純粋な値をそのまま x に束縛

def pureComputation : IO String := do
  -- pure は純粋な値を IO に包む関数
  -- pure "hello" : IO String （"hello" を IO コンテキストに持ち上げる）
  return "計算結果です"  -- return も pure と同じ意味

#eval do
  let result ← pureComputation  -- IO String を実行して String を取り出す
  IO.println s!"結果: {result}"
-- 出力: 結果: 計算結果です

-- ============================================
-- 5. let mut（可変変数）
-- ============================================
-- Lean 4 では do ブロック内で let mut を使って可変変数を宣言できる。
-- 代入には := を使う（再代入も := ）。
--
-- 注意: これは本当の破壊的代入ではなく、コンパイラが
-- 内部的に状態モナドに変換している。ただし使い勝手は
-- 命令型言語の変数とほぼ同じ。

#eval do
  let mut counter := 0         -- 可変変数を宣言
  IO.println s!"初期値: {counter}"
  counter := counter + 1       -- 再代入
  IO.println s!"+1 した: {counter}"
  counter := counter + 10
  IO.println s!"+10 した: {counter}"
  counter := 0                 -- リセット
  IO.println s!"リセット: {counter}"
-- 出力:
-- 初期値: 0
-- +1 した: 1
-- +10 した: 11
-- リセット: 0

-- let（immutable）と let mut（mutable）の違い
#eval do
  let x := 42
  -- x := 99  -- これはコンパイルエラー！ let は再代入不可
  let mut y := 42
  y := 99     -- let mut なら OK
  IO.println s!"x = {x}, y = {y}"
-- 出力: x = 42, y = 99

-- ============================================
-- 6. for ループ
-- ============================================
-- do ブロック内で for ... in ... do 構文が使える。
-- Python の for と同じ感覚で書ける。

-- 6.1 リストに対する for ループ
#eval show IO Unit from do
  let fruits := ["りんご", "みかん", "バナナ"]
  for fruit in fruits do
    IO.println s!"フルーツ: {fruit}"
-- 出力:
-- フルーツ: りんご
-- フルーツ: みかん
-- フルーツ: バナナ

-- 6.2 Range に対する for ループ
-- List.range n は [0, 1, ..., n-1] を生成する
-- [:n] は List.range n の糖衣構文
#eval do
  IO.println "--- List.range を使う ---"
  for i in List.range 5 do
    IO.println s!"  i = {i}"
-- 出力:
-- --- List.range を使う ---
--   i = 0
--   i = 1
--   i = 2
--   i = 3
--   i = 4

-- 6.3 for ループ内で可変変数を更新する
-- 典型的なパターン: 合計を求める
#eval show IO Unit from do
  let mut sum := 0
  for i in List.range 10 do
    sum := sum + (i + 1)  -- 1 + 2 + ... + 10
  IO.println s!"1から10の合計: {sum}"
-- 出力: 1から10の合計: 55

-- 6.4 ネストした for ループ（九九の一部）
#eval show IO Unit from do
  for i in List.range 3 do
    let row := i + 1
    let mut line := s!"{row} の段: "
    for j in List.range 3 do
      let col := j + 1
      let product := row * col
      line := line ++ s!"{row}x{col}={product}  "
    IO.println line
-- 出力:
-- 1 の段: 1x1=1  1x2=2  1x3=3
-- 2 の段: 2x1=2  2x2=4  2x3=6
-- 3 の段: 3x1=3  3x2=6  3x3=9

-- ============================================
-- 7. while ループ（燃料/上限付き）
-- ============================================
-- Lean 4 は停止性を証明する必要がある言語なので、
-- 無限ループは基本的に許されない。
-- do ブロック内の while には自動的に「燃料 (fuel)」が設定され
-- デフォルトで 1000 回で停止する（partial も利用可能）。
--
-- Lean 4 では repeat / while を使うが、
-- 停止性証明が不要な場合は partial を付ける。

-- 7.1 手動で燃料を管理するパターン（最も安全）
#eval show IO Unit from do
  let mut i := 0
  let limit := 10  -- 上限を設ける
  let mut result := ""
  while i < limit do
    result := result ++ s!"{i} "
    i := i + 1
  IO.println s!"while の結果: {result}"
-- 出力: while の結果: 0 1 2 3 4 5 6 7 8 9

-- 7.2 repeat ... break パターン
-- repeat は条件なしで繰り返し、break で脱出する
#eval show IO Unit from do
  let mut n := 1
  repeat
    if n > 5 then
      break
    IO.println s!"repeat: n = {n}"
    n := n + 1
-- 出力:
-- repeat: n = 1
-- repeat: n = 2
-- repeat: n = 3
-- repeat: n = 4
-- repeat: n = 5

-- 7.3 コラッツ数列（3n+1問題）を while で計算
-- 任意の正整数から始めて、偶数なら÷2、奇数なら3n+1 を繰り返すと
-- 最終的に 1 に到達すると予想されている（未証明の有名問題）
#eval do
  let mut n := 27    -- 開始値
  let mut steps := 0
  let mut maxVal := n
  IO.println s!"コラッツ数列: 開始値 = {n}"
  while n != 1 do
    if n % 2 == 0 then
      n := n / 2
    else
      n := 3 * n + 1
    steps := steps + 1
    if n > maxVal then
      maxVal := n
  IO.println s!"  ステップ数: {steps}"
  IO.println s!"  途中の最大値: {maxVal}"
-- 出力:
-- コラッツ数列: 開始値 = 27
--   ステップ数: 111
--   途中の最大値: 9232

-- ============================================
-- 8. if / else（条件分岐）
-- ============================================
-- do ブロック内の if は式としても文としても使える。

-- 8.1 文としての if（副作用を実行するかどうかを分岐）
#eval do
  let temperature := 35
  if temperature >= 35 then
    IO.println "猛暑日です！水分補給を忘れずに"
  else if temperature >= 25 then
    IO.println "夏日です"
  else
    IO.println "過ごしやすい気温です"
-- 出力: 猛暑日です！水分補給を忘れずに

-- 8.2 式としての if（値を返す）
#eval do
  let score := 85
  let grade := if score >= 90 then "A"
               else if score >= 80 then "B"
               else if score >= 70 then "C"
               else "D"
  IO.println s!"スコア: {score}, 評価: {grade}"
-- 出力: スコア: 85, 評価: B

-- 8.3 if と可変変数の組み合わせ
#eval show IO Unit from do
  let numbers := [3, 7, 2, 9, 1, 5, 8, 4, 6]
  let mut evenCount := 0
  let mut oddCount := 0
  for n in numbers do
    if n % 2 == 0 then
      evenCount := evenCount + 1
    else
      oddCount := oddCount + 1
  IO.println s!"偶数: {evenCount}個, 奇数: {oddCount}個"
-- 出力: 偶数: 3個, 奇数: 6個

-- ============================================
-- 9. IO アクションからの値の返却（return / pure）
-- ============================================
-- IO α 型の関数から値を返すには return または pure を使う。
-- return と pure はほぼ同じ意味。return は do ブロック専用の糖衣構文。

-- 9.1 return で値を返す
def computeSum (n : Nat) : IO Nat := do
  let mut sum := 0
  for i in List.range n do
    sum := sum + (i + 1)
  return sum  -- IO Nat 型として sum を返す

#eval do
  let total ← computeSum 100
  IO.println s!"1から100の合計: {total}"
-- 出力: 1から100の合計: 5050

-- 9.2 pure で値を返す（return と同義）
def greetWithName (name : String) : IO String := do
  let greeting := s!"こんにちは、{name}さん！"
  IO.println greeting          -- 副作用: 画面出力
  pure greeting                -- 値としても返す

#eval do
  let msg ← greetWithName "田中"
  IO.println s!"返ってきたメッセージ: {msg}"
-- 出力:
-- こんにちは、田中さん！
-- 返ってきたメッセージ: こんにちは、田中さん！

-- 9.3 早期 return（do ブロックの途中で抜ける）
-- Lean 4 の return は do ブロックの途中で抜けることもできる
def findFirstEven (xs : List Nat) : IO (Option Nat) := do
  for x in xs do
    if x % 2 == 0 then
      IO.println s!"最初の偶数を発見: {x}"
      return some x  -- ここで do ブロックを抜ける
  IO.println "偶数が見つかりませんでした"
  return none

#eval do
  let result ← findFirstEven [1, 3, 5, 4, 6]
  IO.println s!"結果: {result}"
-- 出力:
-- 最初の偶数を発見: 4
-- 結果: some 4

#eval do
  let result ← findFirstEven [1, 3, 5, 7]
  IO.println s!"結果: {result}"
-- 出力:
-- 偶数が見つかりませんでした
-- 結果: none

-- ============================================
-- 10. ユーザー入力（IO.getStdin）
-- ============================================
-- 標準入力からの読み込みは IO.getStdin と .getLine で行う。
-- #eval ではインタラクティブ入力が動かないため、
-- 実際に試すには main 関数から実行する必要がある。

-- 以下はコンパイルは通るが、#eval での実行は意図通り動かないので
-- コメントで実行例を示す。

-- 10.1 基本的な入力読み取り
def askName : IO Unit := do
  IO.print "お名前を入力してください: "
  -- stdout をフラッシュして、プロンプトを確実に表示する
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine          -- 1行読み取り（末尾に改行を含む）
  let name := input.trim              -- 改行を除去
  IO.println s!"ようこそ、{name}さん！"

-- 実行例（main から呼び出した場合）:
-- お名前を入力してください: 太郎
-- ようこそ、太郎さん！

-- 10.2 数値入力の例
def askAge : IO Unit := do
  IO.print "年齢を入力してください: "
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let ageStr := input.trim
  -- String.toNat? は String → Option Nat を返す
  match ageStr.toNat? with
  | some age =>
    if age >= 20 then
      IO.println s!"{age}歳: 成人です"
    else
      IO.println s!"{age}歳: 未成年です"
  | none =>
    IO.println s!"'{ageStr}' は数値ではありません"

-- ============================================
-- 11. try / catch（エラーハンドリング）
-- ============================================
-- Lean 4 では IO アクション中のエラーを try/catch で捕捉できる。
-- IO.Error 型のエラーが投げられると catch ブロックで処理する。

-- 11.1 throw と try/catch の基本
def riskyOperation (n : Nat) : IO Nat := do
  if n == 0 then
    throw (IO.Error.userError "ゼロは受け付けません！")
  return 100 / n

#eval do
  -- 正常系
  try
    let result ← riskyOperation 5
    IO.println s!"結果: {result}"
  catch e =>
    IO.println s!"エラー: {e}"
-- 出力: 結果: 20

#eval do
  -- エラー系
  try
    let result ← riskyOperation 0
    IO.println s!"結果: {result}"
  catch e =>
    IO.println s!"エラー: {e}"
-- 出力: エラー: ゼロは受け付けません！

-- 11.2 ファイル読み込みの例（ファイルが存在しない場合のエラー処理）
def readFileContent (path : String) : IO String := do
  try
    let content ← IO.FS.readFile path
    return content
  catch _ =>
    return s!"(ファイル '{path}' を読めませんでした)"

#eval do
  let content ← readFileContent "/tmp/nonexistent_file_12345.txt"
  IO.println content
-- 出力: (ファイル '/tmp/nonexistent_file_12345.txt' を読めませんでした)

-- 11.3 finally（必ず実行される処理）
-- try/catch/finally も使える
def withCleanup : IO Unit := do
  try
    IO.println "処理開始"
    throw (IO.Error.userError "何かが失敗しました")
  catch e =>
    IO.println s!"エラーを捕捉: {e}"
  finally
    IO.println "クリーンアップ処理（必ず実行）"

#eval withCleanup
-- 出力:
-- 処理開始
-- エラーを捕捉: 何かが失敗しました
-- クリーンアップ処理（必ず実行）

-- ============================================
-- 12. 純粋関数と IO の組み合わせ
-- ============================================
-- Lean 4 の設計思想: ロジックは純粋関数で書き、
-- IO は入出力の「接着剤」としてだけ使う。

-- 12.1 純粋関数を定義（IO に依存しない）
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    -- 2 から n-1 まで試し割り
    let candidates := List.range (n - 2) |>.map (· + 2)
    candidates.all fun d => n % d != 0

def formatPrimeResult (n : Nat) : String :=
  if isPrime n then s!"{n} は素数です"
  else s!"{n} は素数ではありません"

-- 12.2 純粋関数を IO の中で使う
#eval show IO Unit from do
  let numbers := [1, 2, 3, 4, 5, 11, 15, 17, 20, 23]
  for n in numbers do
    IO.println (formatPrimeResult n)
-- 出力:
-- 1 は素数ではありません
-- 2 は素数です
-- 3 は素数です
-- 4 は素数ではありません
-- 5 は素数です
-- 11 は素数です
-- 15 は素数ではありません
-- 17 は素数です
-- 20 は素数ではありません
-- 23 は素数です

-- 12.3 純粋関数によるデータ変換パイプライン
def tokenize (s : String) : List String :=
  s.splitOn " " |>.filter (· != "")

def countWords (s : String) : Nat :=
  (tokenize s).length

def capitalize (s : String) : String :=
  match s.toList with
  | []      => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

#eval do
  let sentence := "lean is a functional programming language"
  let words := tokenize sentence
  let count := countWords sentence
  let capitalized := words.map capitalize
  IO.println s!"原文: {sentence}"
  IO.println s!"単語数: {count}"
  IO.println s!"先頭大文字化: {capitalized}"
-- 出力:
-- 原文: lean is a functional programming language
-- 単語数: 6
-- 先頭大文字化: [Lean, Is, A, Functional, Programming, Language]

-- ============================================
-- 13. IO の型パズル: ← と := の使い分け
-- ============================================
-- 初学者がつまずきやすいポイントをまとめる

-- ケース1: 純粋な計算 → := を使う
-- ケース2: IO アクションの結果 → ← を使う

#eval show IO Unit from do
  -- := の例（純粋な値の束縛）
  let x : Nat := 1 + 2               -- Nat
  let name : String := "太郎"            -- String
  let list : List Nat := [1, 2, 3]        -- List Nat
  let doubled := list.map (· * 2) -- List Nat

  -- ← の例（IO アクションの実行結果を取り出す）
  -- let stdin ← IO.getStdin      -- IO.FS.Stream を取り出す
  -- let line ← stdin.getLine     -- String を取り出す（インタラクティブなのでコメントアウト）

  IO.println s!"x = {x}"
  IO.println s!"name = {name}"
  IO.println s!"doubled = {doubled}"

  -- もし ← と := を間違えると…
  -- let wrong := IO.println "test"  -- wrong の型は IO Unit（実行されない！）
  -- let right ← IO.println "test"  -- 実行される。right の型は Unit

  -- 間違いの例をわかりやすく:
  let action := IO.println "これは実行されない（IO Unit 型の値として束縛されるだけ）"
  -- ↑ action は IO Unit 型の値。まだ実行されていない！
  -- 実行するには:
  action  -- do ブロック内でそのまま書けば実行される
-- 出力:
-- x = 1 + 2 の結果 = 3
-- ... (上記出力が表示される)

-- ============================================
-- 14. 実践例: 小さな CLI プログラム
-- ============================================

-- 14.1 タスクリスト管理（簡易版）
-- 実際の入力は使わず、ハードコードで動作を示す

structure TodoItem where
  id   : Nat
  name : String
  done : Bool
deriving Repr

instance : ToString TodoItem where
  toString t :=
    let status := if t.done then "[x]" else "[ ]"
    s!"{status} #{t.id}: {t.name}"

def showTasks (tasks : List TodoItem) : IO Unit := do
  IO.println "=== タスクリスト ==="
  if tasks.isEmpty then
    IO.println "  (タスクなし)"
  else
    for t in tasks do
      IO.println s!"  {t}"
  IO.println ""

def addTask (tasks : List TodoItem) (name : String) : List TodoItem :=
  let newId := match tasks.map (·.id) |>.max? with
    | some maxId => maxId + 1
    | none       => 1
  tasks ++ [{ id := newId, name := name, done := false }]

def completeTask (tasks : List TodoItem) (id : Nat) : List TodoItem :=
  tasks.map fun t =>
    if t.id == id then { t with done := true } else t

def removeCompleted (tasks : List TodoItem) : List TodoItem :=
  tasks.filter (!·.done)

#eval do
  IO.println "--- タスク管理デモ ---"
  IO.println ""

  -- 初期状態
  let mut tasks : List TodoItem := []
  showTasks tasks

  -- タスク追加
  IO.println "[操作] タスクを3つ追加"
  tasks := addTask tasks "Lean 4 のインストール"
  tasks := addTask tasks "チュートリアルを読む"
  tasks := addTask tasks "最初のプログラムを書く"
  showTasks tasks

  -- タスク完了
  IO.println "[操作] タスク #1 を完了"
  tasks := completeTask tasks 1
  showTasks tasks

  -- もう1つ完了
  IO.println "[操作] タスク #3 を完了"
  tasks := completeTask tasks 3
  showTasks tasks

  -- 完了済みを削除
  IO.println "[操作] 完了済みタスクを削除"
  tasks := removeCompleted tasks
  showTasks tasks

  IO.println "--- デモ終了 ---"

-- 14.2 テキスト統計（純粋関数 + IO の実践例）

structure TextStats where
  chars     : Nat
  words     : Nat
  lines     : Nat
  sentences : Nat

instance : ToString TextStats where
  toString s :=
    s!"文字数: {s.chars}, 単語数: {s.words}, 行数: {s.lines}, 文数: {s.sentences}"

-- 純粋関数: テキストの統計を計算
def analyzeText (text : String) : TextStats :=
  let chars := text.length
  let words := text.splitOn " " |>.filter (· != "") |>.length
  let lines := text.splitOn "\n" |>.length
  let sentences := text.toList.filter (fun c => c == '.' || c == '!' || c == '?') |>.length
  { chars, words, lines, sentences }

-- IO 関数: 結果を表示
def showTextAnalysis (label : String) (text : String) : IO Unit := do
  IO.println s!"--- {label} ---"
  IO.println s!"テキスト: \"{text}\""
  let stats := analyzeText text  -- 純粋関数を呼ぶ（← 不要）
  IO.println s!"統計: {stats}"
  IO.println ""

#eval do
  showTextAnalysis "英文サンプル"
    "Hello world. This is Lean 4. It is great!"
  showTextAnalysis "短いテキスト"
    "OK"
  showTextAnalysis "複数行"
    "Line one.\nLine two.\nLine three."

-- ============================================
-- 15. main 関数の書き方
-- ============================================
-- Lean 4 のプログラムのエントリポイントは main : IO Unit。
-- 本ファイルはライブラリとして使うので main は定義しないが、
-- 以下に典型的な main 関数のパターンを示す。

/-
-- パターン1: シンプルな main
def main : IO Unit := do
  IO.println "Hello, World!"

-- パターン2: コマンドライン引数を受け取る main
def main (args : List String) : IO Unit := do
  IO.println s!"引数の数: {args.length}"
  for arg in args do
    IO.println s!"  引数: {arg}"

-- パターン3: エラーハンドリング付き main
def main : IO Unit := do
  try
    let content ← IO.FS.readFile "input.txt"
    IO.println s!"ファイル内容: {content}"
  catch e =>
    IO.eprintln s!"エラー: {e}"  -- 標準エラー出力

-- パターン4: 終了コードを返す main
def main : IO UInt32 := do
  try
    -- 何かの処理
    return 0   -- 成功
  catch _ =>
    return 1   -- 失敗
-/

-- ============================================
-- まとめ
-- ============================================
-- 1. IO α は「副作用を起こして α を返すアクション」
-- 2. do ブロックで命令型風にコードを書ける
-- 3. let := は純粋な値、let ← は IO アクション結果の束縛
-- 4. let mut で可変変数を宣言し、:= で再代入
-- 5. for / while / repeat で繰り返し処理
-- 6. try/catch/finally でエラーハンドリング
-- 7. ロジックは純粋関数で書き、IO は入出力の接着剤として使う
-- 8. main : IO Unit がプログラムのエントリポイント
--
-- 他言語との対応:
--   IO Unit    ≈  void / undefined
--   ←          ≈  await (TypeScript) / <- (Haskell)
--   let mut    ≈  let (JavaScript) / var (Python的)
--   let        ≈  const (JavaScript)
--   return     ≈  return (各言語共通)
--   do ブロック ≈  async function のボディ

end Tutorial08
