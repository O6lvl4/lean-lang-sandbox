-- ============================================================
-- Tutorial09_Proofs.lean
-- Lean 4 定理証明チュートリアル（日本語解説付き）
--
-- 対象読者: 他の言語（TypeScript, Python, Rustなど）は書けるが、
--           Lean や定理証明は初めての開発者
--
-- このファイル単体でコンパイルが通ります。
-- コンパイルが通る = すべての証明が正しい、ということです。
-- ============================================================

namespace Tutorial09

-- ////////////////////////////////////////////////////////////
-- 第1章: Prop とは何か？ ── 命題は「型」である
-- ////////////////////////////////////////////////////////////

/-!
# 命題（Proposition）と型の対応

普通のプログラミング言語では、型は「値の集合」を表します。
  - `Nat` は 0, 1, 2, 3, ... という値の集合
  - `String` は "hello", "world", ... という値の集合
  - `Bool` は true, false の2つだけ

Lean では **命題（Prop）も型** として扱います。
  - `2 + 3 = 5` は型。この型の「値」（＝証拠）が存在すれば、命題は真。
  - `2 + 3 = 6` も型。この型の値は存在しない → 命題は偽。

つまり：
  - **命題を証明する = その型の値（項）を構成する**
  - **証明が存在しない = その型の値が作れない**

これを「カリー＝ハワード対応（Curry-Howard Correspondence）」と呼びます。
TypeScriptで例えると、「型エラーが出なければ正しい」の究極版です。
-/

-- `Prop` は命題の宇宙（Universe）。命題の型です。
-- 以下は「Prop 型の値」を宣言しているだけ。真偽はまだ問わない。
-- 他の言語でいう interface や abstract type の宣言に近い。
section PropDemo
  variable (P Q R : Prop)

  -- P, Q, R はそれぞれ何らかの命題を表す。
  -- 例: P = 「2は偶数である」, Q = 「3は素数である」 など。
  -- ここでは中身を決めず、一般的な命題として扱う。

  -- `P → Q` は「PならばQ」。
  -- 型の世界では「Pの証拠を受け取ってQの証拠を返す関数」。
  -- つまり **含意（implication）= 関数型** ！

  -- `P ∧ Q` は「PかつQ」。型の世界では「Pの証拠とQの証拠のペア」。
  -- つまり **論理積 = 直積型（タプル/構造体）** ！

  -- `P ∨ Q` は「PまたはQ」。型の世界では「Pの証拠かQの証拠のどちらか」。
  -- つまり **論理和 = 直和型（Either/enum）** ！
end PropDemo


-- ////////////////////////////////////////////////////////////
-- 第2章: True と False ── 自明な命題と不可能な命題
-- ////////////////////////////////////////////////////////////

/-!
# True と False

`True` は常に真の命題。証拠は `True.intro` （または `trivial`）で作れる。
→ 他の言語で言う「Unit型」に相当。値がただ1つ存在する。

`False` は常に偽の命題。証拠を構成する方法がない。
→ 他の言語で言う「Never型」「Bottom型」に相当。値が存在しない。

`False` の証拠があれば、何でも証明できる（爆発原理/Ex Falso）。
→ 「矛盾から任意の命題が導ける」という論理学の基本原理。
-/

-- True は簡単に証明できる
theorem true_is_trivial : True :=
  True.intro  -- True の唯一の証拠（コンストラクタ）

-- False からは何でも導ける（爆発原理）
-- 「もし False が証明できたら、何でも言える」ということ
theorem false_implies_anything (P : Prop) : False → P :=
  fun h => False.elim h  -- False.elim : False → α（任意の型の値を返せる）
  -- False の証拠 h は実際には存在し得ないので、
  -- この関数が「呼ばれること」は絶対にない。
  -- だから返す値を作れなくても大丈夫（空虚な真）。


-- ////////////////////////////////////////////////////////////
-- 第3章: theorem キーワード
-- ////////////////////////////////////////////////////////////

/-!
# theorem キーワード

`theorem` は `def` とほぼ同じ。値を定義します。
ただし以下の違いがあります：

1. `theorem` はその値が Prop 型であることを期待する
2. `theorem` で定義された値はカーネルが証明をチェックした後、
   証明の中身を捨てて効率化できる（proof irrelevance）
3. 読む人に「これは証明である」と意図を伝える

構文:
  theorem 名前 (仮定) : 命題 := 証明の項

`def` で書いても型チェックは通りますが、慣習として命題の証明には
`theorem` を使います。
-/

-- def で書いても全く同じことができる（が、theorem の方が意図が明確）
def identity_def (P : Prop) : P → P :=
  fun h => h

-- theorem で書いた方が「これは証明です」と一目で分かる
theorem identity_thm (P : Prop) : P → P :=
  fun h => h


-- ////////////////////////////////////////////////////////////
-- 第4章: 項モード証明（Term-mode Proofs）
-- ////////////////////////////////////////////////////////////

/-!
# 項モード証明（Term-mode Proofs）

証明を「式（項）」として直接書くスタイル。
関数型プログラミングに慣れている人にはこちらの方が自然かもしれません。

- `P → Q` の証明 = `P` を受け取って `Q` を返す関数
- `P ∧ Q` の証明 = P の証拠と Q の証拠のペア `⟨hp, hq⟩`
- `P ∨ Q` の証明 = `Or.inl hp` か `Or.inr hq`

パターンマッチ、ラムダ式、関数適用 …… 普通のコードと同じ。
-/

-- ── 含意（→）の証明 ──

-- P → P : 恒等関数そのもの
theorem impl_identity (P : Prop) : P → P :=
  fun hp => hp
  -- hp : P の証拠。そのまま返すだけ。
  -- TypeScriptなら `(p: P) => p` と同じ感覚。

-- P → Q → P : 最初の引数だけ使って2番目は捨てる
-- （Haskellの `const` 関数と同じ形）
theorem impl_const (P Q : Prop) : P → Q → P :=
  fun hp _hq => hp
  -- hp : P の証拠, _hq : Q の証拠（使わない）
  -- P の証拠 hp をそのまま返す。

-- ── 連言（∧）の証明 ──

-- P ∧ Q → Q ∧ P : ペアの要素を入れ替える
-- Rustで言う `(a, b) => (b, a)` のようなもの
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
  -- ⟨hp, hq⟩ で P ∧ Q を分解（パターンマッチ）
  -- ⟨hq, hp⟩ で Q ∧ P を構成

-- P ∧ Q → P : ペアの左側を取り出す
-- （fst / first に相当）
theorem and_left (P Q : Prop) : P ∧ Q → P :=
  fun ⟨hp, _hq⟩ => hp

-- ── 選言（∨）の証明 ──

-- P → P ∨ Q : 左側に入れる
-- TypeScriptの `type Either<L,R> = {tag:"left", val:L} | ...` の Left に相当
theorem or_intro_left (P Q : Prop) : P → P ∨ Q :=
  fun hp => Or.inl hp
  -- Or.inl : P → P ∨ Q （左に注入）

-- P ∨ Q → Q ∨ P : 場合分けして入れ替える
-- switchやmatch式に相当
theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => match h with
    | Or.inl hp => Or.inr hp  -- 左(P)だったら → 右(P)に
    | Or.inr hq => Or.inl hq  -- 右(Q)だったら → 左(Q)に

-- ── 否定（¬）の証明 ──

-- ¬P は「P → False」の省略記法。
-- 「Pが真だと仮定すると矛盾（False）が導ける」＝「Pは偽」

-- ¬False : False → False 。恒等関数でOK。
theorem not_false_term : ¬False :=
  fun h => h
  -- ¬False = False → False なので、受け取った h をそのまま返す。

-- P → ¬¬P : 二重否定の導入
-- ¬¬P = (P → False) → False
-- 「『Pが偽である』と仮定すると矛盾」＝「Pは真」
theorem double_neg_intro_term (P : Prop) : P → ¬¬P :=
  fun hp hnp => hnp hp
  -- hp : P の証拠
  -- hnp : ¬P = P → False
  -- hnp hp で False を得る（矛盾！）


-- ////////////////////////////////////////////////////////////
-- 第5章: タクティクモード証明（Tactic-mode Proofs）
-- ////////////////////////////////////////////////////////////

/-!
# タクティクモード証明（Tactic-mode Proofs）

`by` キーワードで始めると「タクティクモード」に入る。
ゴール（証明すべきこと）を少しずつ変形・分解していくスタイル。

対話的なパズル感覚で証明できるので、初心者にはこちらがおすすめ。
VS Code の Lean 4 拡張を使うと、各行でゴールの状態が見える。

よく使うタクティク：
  - intro : 仮定を導入する（ゴール `P → Q` から P を取り出す）
  - exact : ゴールにぴったり合う項を渡す（証明完了）
  - apply : ゴールに関数/定理を適用する（ゴールを変形）
  - rfl   : ゴールが `a = a` の形ならそれで終了（反射律）
  - constructor : ゴールが `P ∧ Q` なら2つのサブゴールに分ける
  - cases : 仮定を場合分けする（∧の分解、∨の場合分けなど）
  - assumption : 仮定の中にゴールと一致するものがあれば終了
-/

-- ────────────────────────────────────
-- intro タクティク
-- ────────────────────────────────────
-- ゴール: P → P
-- `intro hp` で「P の証拠 hp」を仮定に追加し、ゴールが P になる
theorem impl_identity_tactic (P : Prop) : P → P := by
  intro hp    -- 仮定に hp : P を導入。ゴール: P
  exact hp    -- ゴールと hp が一致 → 完了！

-- ────────────────────────────────────
-- exact タクティク
-- ────────────────────────────────────
-- ゴールにぴったり合う項を直接渡す
theorem impl_const_tactic (P Q : Prop) : P → Q → P := by
  intro hp _hq  -- 仮定: hp : P, _hq : Q。ゴール: P
  exact hp       -- hp がゴール P にぴったり

-- ────────────────────────────────────
-- apply タクティク
-- ────────────────────────────────────
-- ゴールを「逆方向に」変形する。
-- ゴールが Q で、仮定に f : P → Q があるとき、
-- `apply f` でゴールが P に変わる。
-- 「Q を証明するには、f を使えばいいから、P を証明すれば十分」

theorem apply_demo (P Q : Prop) (f : P → Q) (hp : P) : Q := by
  apply f    -- ゴール: Q → P に変わる（f を適用するので P を示せば十分）
  exact hp   -- ゴール: P → hp で完了

-- 連鎖的に apply を使う例
theorem apply_chain (P Q R : Prop) (f : P → Q) (g : Q → R) (hp : P) : R := by
  apply g    -- ゴール: R → Q に変わる
  apply f    -- ゴール: Q → P に変わる
  exact hp   -- ゴール: P → 完了

-- ────────────────────────────────────
-- rfl タクティク
-- ────────────────────────────────────
-- ゴールが `x = x` の形（両辺が定義上等しい）なら rfl で終わる。
-- rfl = reflexivity（反射律）。「同じものは同じ」。

theorem rfl_demo : 42 = 42 := by
  rfl  -- 両辺が同じなので自明

theorem rfl_demo2 : 2 + 3 = 5 := by
  rfl  -- Lean が 2 + 3 を計算して 5 になることを確認

-- ────────────────────────────────────
-- constructor タクティク
-- ────────────────────────────────────
-- ゴールが構造体/帰納型のとき、コンストラクタを適用する。
-- P ∧ Q なら2つのサブゴールに分割される。
-- ⟨_, _⟩ と書くのと同じだが、サブゴールが見やすい。

theorem and_swap_tactic (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h          -- h : P ∧ Q。ゴール: Q ∧ P
  constructor      -- ゴールが2つに分割: (1) Q  (2) P
  · exact h.right  -- サブゴール1: Q → h.right で取得
  · exact h.left   -- サブゴール2: P → h.left で取得
  -- h.left = P の証拠, h.right = Q の証拠
  -- h.1, h.2 とも書ける

-- ────────────────────────────────────
-- cases タクティク
-- ────────────────────────────────────
-- 仮定を場合分け（分解）する。
-- ∧ の分解、∨ の場合分け、帰納型のパターンマッチに使う。

-- cases で ∧ を分解
theorem and_left_tactic (P Q : Prop) : P ∧ Q → P := by
  intro h         -- h : P ∧ Q
  cases h with    -- h を分解
  | intro hp hq =>  -- And.intro hp hq のパターン
    exact hp      -- hp : P でゴール完了

-- cases で ∨ を場合分け
theorem or_swap_tactic (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h          -- h : P ∨ Q
  cases h with     -- h が左(P)か右(Q)かで場合分け
  | inl hp =>      -- h = Or.inl hp のケース。hp : P
    exact Or.inr hp   -- Q ∨ P の右側に P を入れる
  | inr hq =>      -- h = Or.inr hq のケース。hq : Q
    exact Or.inl hq   -- Q ∨ P の左側に Q を入れる

-- ────────────────────────────────────
-- assumption タクティク
-- ────────────────────────────────────
-- 現在の仮定（コンテキスト）の中にゴールと一致するものがあれば、
-- 自動的にそれを使って証明を完了する。
-- 「exact ?????」と書く代わりに、探してもらう感覚。

theorem assumption_demo (P Q : Prop) (hp : P) (_hq : Q) : P := by
  assumption  -- 仮定 hp : P がゴール P と一致 → 完了


-- ////////////////////////////////////////////////////////////
-- 第6章: 論理結合子の証明集
-- ////////////////////////////////////////////////////////////

/-!
# 論理結合子（Logical Connectives）の証明

ここでは各論理結合子について、タクティクモードで丁寧に証明します。
各証明の前に「何を示すのか」「直感的にどういうことか」を説明します。
-/

-- ══════════════════════════════════════
-- 6.1 含意（→）: Implication
-- ══════════════════════════════════════

-- 直感: 「PならばP」── 同じことを仮定すれば当然成り立つ
-- 関数で言えば: 恒等関数 id
theorem implication_identity (P : Prop) : P → P := by
  intro hp   -- P を仮定する
  exact hp   -- その仮定がそのまま証明

-- 直感: 「PならばQならばP」── Pがあれば、Qが何であれPは言える
-- 関数で言えば: const関数 (最初の引数だけ返す)
theorem implication_const (P Q : Prop) : P → Q → P := by
  intro hp _hq   -- P と Q を仮定
  exact hp        -- P を返す（Q は無視）

-- 直感: 含意の推移律（三段論法）
-- 「P→Q」と「Q→R」なら「P→R」
-- 関数で言えば: 関数合成 g ∘ f
theorem implication_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp   -- hpq : P → Q, hqr : Q → R, hp : P
  apply hqr           -- ゴール: R → Q を示せば十分
  apply hpq           -- ゴール: Q → P を示せば十分
  exact hp            -- P は仮定にある

-- ══════════════════════════════════════
-- 6.2 論理積（∧）: And / Conjunction
-- ══════════════════════════════════════

-- 直感: 「PかつQ」なら「QかつP」── 順番を入れ替えても意味は同じ
theorem and_comm_tut (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h          -- h : P ∧ Q
  constructor      -- ゴールを Q と P に分割
  · exact h.right  -- Q は h の右側
  · exact h.left   -- P は h の左側

-- 直感: 「PかつQ」なら「P」── ペアから一方を取り出す
theorem and_elim_left (P Q : Prop) : P ∧ Q → P := by
  intro h       -- h : P ∧ Q
  exact h.left  -- ペアの左側を取り出す

-- 直感: 「PかつQ」なら「Q」── 逆側を取り出す
theorem and_elim_right (P Q : Prop) : P ∧ Q → Q := by
  intro h        -- h : P ∧ Q
  exact h.right  -- ペアの右側を取り出す

-- 直感: P, Q, R の3つ全部が成り立つなら、順番を変えても同じ
theorem my_and_assoc (P Q R : Prop) : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro ⟨⟨hp, hq⟩, hr⟩  -- ネストしたペアを一気に分解
  exact ⟨hp, hq, hr⟩     -- 組み替えて返す

-- ══════════════════════════════════════
-- 6.3 論理和（∨）: Or / Disjunction
-- ══════════════════════════════════════

-- 直感: 「P」ならば「PまたはQ」── 片方が成り立てば「または」は成り立つ
-- TypeScriptで言えば: `P | Q` 型の値を P だけで作れる
theorem or_intro_left_tut (P Q : Prop) : P → P ∨ Q := by
  intro hp          -- hp : P
  exact Or.inl hp   -- 左側に入れる（Left injection）

-- 直感: 同様に右側からも入れられる
theorem or_intro_right_tut (P Q : Prop) : Q → P ∨ Q := by
  intro hq          -- hq : Q
  exact Or.inr hq   -- 右側に入れる（Right injection）

-- 直感: 「PまたはQ」なら「QまたはP」── 順番を入れ替えるだけ
theorem or_comm_tut (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h         -- h : P ∨ Q
  cases h with    -- P か Q かで場合分け
  | inl hp =>     -- Case 1: P が成り立つ
    right         -- Q ∨ P の右側（= P）を選ぶ （`right` = `exact Or.inr`の糖衣構文）
    exact hp
  | inr hq =>     -- Case 2: Q が成り立つ
    left          -- Q ∨ P の左側（= Q）を選ぶ
    exact hq

-- ══════════════════════════════════════
-- 6.4 否定（¬）: Not / Negation
-- ══════════════════════════════════════

/-!
復習: `¬P` は `P → False` の定義。
「Pが真だと仮定すると矛盾が導ける」＝「Pは偽」
-/

-- 直感: ¬False = False → False。「偽は偽である」── 自明
theorem not_false_tut : ¬False := by
  intro h     -- h : False（偽だと仮定する）
  exact h     -- ゴールも False なのでそのまま（実際にはありえない仮定）

-- 直感: P → ¬¬P。「Pが真なら、Pを否定すると矛盾する」
-- ¬¬P = (P → False) → False
-- 「Pが偽だという主張」と「Pが真である証拠」を合わせると矛盾
theorem double_neg_intro_tut (P : Prop) : P → ¬¬P := by
  intro hp     -- hp : P
  intro hnp    -- hnp : ¬P = P → False
  exact hnp hp -- hnp に hp を適用 → False（矛盾！）

-- 直感: 対偶。「P→Q」ならば「¬Q→¬P」
-- 「QでないのにPだったら、P→QからQが出て矛盾」
theorem contrapositive_tut (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hpq    -- hpq : P → Q
  intro hnq    -- hnq : ¬Q = Q → False
  intro hp     -- hp : P （¬P = P → False を示すため）
  apply hnq    -- ゴール: False → Q を示せば十分
  apply hpq    -- ゴール: Q → P を示せば十分
  exact hp     -- P は仮定にある

-- 直感: 矛盾（PかつPの否定）から何でも導ける
theorem absurd_demo (P Q : Prop) : P → ¬P → Q := by
  intro hp hnp  -- hp : P, hnp : ¬P
  exact absurd hp hnp
  -- absurd : α → ¬α → β （矛盾があれば何でも証明できる）

-- ══════════════════════════════════════
-- 6.5 同値（↔）: Iff / If and Only If
-- ══════════════════════════════════════

/-!
`P ↔ Q` は `(P → Q) ∧ (Q → P)` と同じ。
「PならばQ」かつ「QならばP」＝「PとQは同値」。

証明するには両方向を示す必要がある。
`constructor` で2つのサブゴールに分けられる。
-/

-- 直感: 「PかつQ」と「QかつP」は同値
-- （当然だが、両方向きちんと示す必要がある）
theorem and_comm_iff (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor                      -- 2つのサブゴール: (→) と (←)
  · intro ⟨hp, hq⟩                -- (→) P ∧ Q → Q ∧ P
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩                -- (←) Q ∧ P → P ∧ Q
    exact ⟨hp, hq⟩

-- 直感: 「PまたはQ」と「QまたはP」は同値
theorem or_comm_iff (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- 直感: P ↔ P は当然成り立つ（同値の反射律）
theorem iff_refl (P : Prop) : P ↔ P := by
  constructor
  · intro hp; exact hp  -- P → P
  · intro hp; exact hp  -- P → P


-- ////////////////////////////////////////////////////////////
-- 第7章: have ── 証明の中で中間補題を作る
-- ////////////////////////////////////////////////////////////

/-!
# have タクティク

長い証明では、途中で中間的な事実（補題）を示したいことがある。
`have` を使うと「証明の中で一時的な定理」を宣言できる。

プログラミングで言えば「ローカル変数」に相当。
中間結果に名前をつけて、後で使う。
-/

-- 含意の推移を have を使って丁寧に書く
theorem trans_with_have (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  -- まず中間結果として Q の証拠を作る
  have hq : Q := hpq hp    -- hpq に hp を適用して Q を得る
  -- 次に Q から R を得る
  have hr : R := hqr hq    -- hqr に hq を適用して R を得る
  -- 最終ゴール R は hr で証明済み
  exact hr

-- もう少し複雑な例: P ∧ Q ∧ R → R ∧ P
-- 中間で各要素を取り出して名前をつける
theorem extract_and_rearrange (P Q R : Prop) : P ∧ Q ∧ R → R ∧ P := by
  intro h
  have hp : P := h.left          -- P ∧ (Q ∧ R) の左側 = P
  have hqr : Q ∧ R := h.right    -- P ∧ (Q ∧ R) の右側 = Q ∧ R
  have hr : R := hqr.right        -- Q ∧ R の右側 = R
  exact ⟨hr, hp⟩                  -- R ∧ P を構成


-- ////////////////////////////////////////////////////////////
-- 第8章: 自然数（Nat）の簡単な証明
-- ////////////////////////////////////////////////////////////

/-!
# 自然数の証明

Lean での自然数 `Nat` は：
  - `Nat.zero` (= 0)
  - `Nat.succ n` (= n + 1)
の2つのコンストラクタで定義される帰納型。

加算 `Nat.add` は左側の引数で再帰的に定義されている：
  - `0 + n = n`        (定義そのまま)
  - `(m+1) + n = (m + n) + 1`  (再帰)

このため `0 + n = n` は rfl で証明できるが、
`n + 0 = n` は帰納法が必要になる（右側の 0 は定義で消えないため）。
-/

-- 0 + n = n : 定義から自明（rfl で終わる）
theorem zero_add_tut (n : Nat) : 0 + n = n := by
  simp [Nat.add]
  -- Lean 4 v4.28.0 では rfl では簡約されないため simp を使用

-- n = n : 当然
theorem eq_refl_nat (n : Nat) : n = n := by
  rfl

-- 1 + 1 = 2 : 計算で確認
theorem one_plus_one : 1 + 1 = 2 := by
  rfl  -- 1 + 1 は Nat.succ (Nat.succ 0) = 2

-- 具体的な数値の等式
theorem concrete_calc : 3 + 4 = 7 := by
  rfl  -- Lean が計算して確認

-- n + 0 = n : 帰納法が必要
-- 左辺の n + 0 は定義で簡約されないため、n について場合分けする
theorem add_zero_tut (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
    -- ゴール: 0 + 0 = 0
    rfl
  | succ k ih =>
    -- ih : k + 0 = k（帰納法の仮定）
    -- ゴール: (k + 1) + 0 = k + 1
    -- (k+1) + 0 = (k + 0) + 1 = k + 1（ih を使う）
    simp [ih]
    -- simp が ih を使って書き換えてくれる


-- ////////////////////////////////////////////////////////////
-- 第9章: simp タクティク
-- ////////////////////////////////////////////////////////////

/-!
# simp タクティク（Simplification）

`simp` は Lean 最強の自動化タクティクの一つ。
登録された補題（simp lemma）を使って、ゴールを自動的に簡約する。

- `simp` : デフォルトの simp 補題集を使って簡約
- `simp [h]` : 仮定 h や定理名を追加で使って簡約
- `simp only [h1, h2]` : 指定した補題だけを使って簡約

「とりあえず simp で試す」のは Lean の証明でよくあるパターン。
ただし、simp に頼りすぎると証明が遅くなったり壊れやすくなることも。
-/

-- simp が自動的に処理してくれる例
theorem simp_demo1 : 0 + 5 = 5 := by
  simp  -- 0 + n = n は simp の知識に含まれている

theorem simp_demo2 (n : Nat) : n + 0 = n := by
  simp  -- n + 0 = n も simp が知っている

theorem simp_demo3 (n : Nat) : 0 + n + 0 = n := by
  simp  -- 複数の簡約を一度にやってくれる

-- リストの簡約例
theorem simp_list : [1, 2, 3].length = 3 := by
  simp  -- リストの length を計算して簡約

-- 仮定を simp に渡す例
theorem simp_with_hyp (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  simp [h]  -- h : n = m を使って n を m に書き換え、あとは rfl

-- Bool の簡約
theorem simp_bool : (true && false) = false := by
  simp


-- ////////////////////////////////////////////////////////////
-- 第10章: omega タクティク
-- ////////////////////////////////////////////////////////////

/-!
# omega タクティク

`omega` は **線形算術（linear arithmetic）** を自動で解くタクティク。
自然数や整数の等式・不等式で、加算・減算・定数倍だけで表現できるものなら、
omega が自動的に証明してくれる。

TypeScriptで言えば「型チェッカが算術も理解してくれる」ような感覚。

使える場面：
  - `n + m = m + n` のような加法の性質
  - `n < n + 1` のような不等式
  - `n ≥ 0` のような自明な事実

使えない場面：
  - 乗算を含む非線形な式（`n * m = m * n` など）
-/

-- 加法の交換法則
theorem add_comm_nat (n m : Nat) : n + m = m + n := by
  omega  -- 線形算術なので omega で一発

-- 加法の結合法則
theorem add_assoc_nat (n m k : Nat) : (n + m) + k = n + (m + k) := by
  omega

-- 不等式
theorem succ_gt (n : Nat) : n < n + 1 := by
  omega

-- 0 以上は自明
theorem nat_nonneg (n : Nat) : 0 ≤ n := by
  omega

-- 複合的な算術
theorem arith_combo (a b : Nat) : a + b + 1 = 1 + a + b := by
  omega

-- 仮定を使った算術
theorem arith_with_hyp (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by
  omega  -- h : n ≤ m から n ≤ m + 1 を自動で導く

-- 整数（Int）でも使える
theorem int_arith (a b : Int) : a + b = b + a := by
  omega


-- ////////////////////////////////////////////////////////////
-- 第11章: decide タクティク
-- ////////////////////////////////////////////////////////////

/-!
# decide タクティク

`decide` は **決定可能な命題（Decidable Proposition）** を
計算によってtrue/falseを判定し、証明するタクティク。

「実際に計算してみて、trueなら証明完了」というブルートフォース的な手法。

使える場面：
  - 具体的な数値の比較: `2 < 5`, `10 = 10`
  - Bool 式の評価: `(3 % 2 == 1) = true`
  - 有限な場合分け

使えない場面：
  - 変数を含む一般的な命題: `∀ n, n + 0 = n`
  - 計算量が膨大になるもの

TypeScriptで例えると: `as const` で具体値を確定させて型チェックする感覚。
-/

-- 具体的な数値の等式
theorem decide_eq : (2 + 3 : Nat) = 5 := by decide
-- decide は実際に 2 + 3 を計算して 5 になることを確認する

-- 具体的な不等式
theorem decide_lt : (3 : Nat) < 10 := by decide

-- Bool の評価
theorem decide_bool : (10 % 3 == 1) = true := by decide

-- 否定の決定
theorem decide_neq : (2 : Nat) ≠ 3 := by decide

-- 論理演算の具体的な評価
theorem decide_logic : (true || false) = true := by decide

-- 小さいリストの性質
theorem decide_list : [1, 2, 3].length = 3 := by decide

-- 有限な場合分け（小さい数なら decide で解ける）
theorem small_cases : ∀ n : Fin 3, n.val < 5 := by decide
-- Fin 3 は {0, 1, 2} の3通りしかないので、全部試して確認できる


-- ////////////////////////////////////////////////////////////
-- 第12章: 総合演習 ── 色々なテクニックを組み合わせる
-- ////////////////////////////////////////////////////////////

/-!
# 総合演習

ここまで学んだテクニックを組み合わせた証明をいくつか示します。
各証明には複数のタクティクが登場します。
-/

-- ── ド・モルガンの法則（片方向） ──
-- 直感: 「PでもQでもない」ならば「Pでない、かつ、Qでない」
theorem de_morgan_not_or (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h               -- h : ¬(P ∨ Q) = (P ∨ Q) → False
  constructor           -- ゴール: ¬P ∧ ¬Q → 2つのサブゴール
  · -- サブゴール1: ¬P = P → False
    intro hp            -- hp : P と仮定
    apply h             -- ゴール: P ∨ Q を示せば False が出る
    exact Or.inl hp     -- P → P ∨ Q
  · -- サブゴール2: ¬Q = Q → False
    intro hq            -- hq : Q と仮定
    apply h             -- ゴール: P ∨ Q を示せば False が出る
    exact Or.inr hq     -- Q → P ∨ Q

-- ── ド・モルガンの法則（逆方向） ──
-- 直感: 「Pでない、かつ、Qでない」ならば「PでもQでもない」
theorem de_morgan_not_or_rev (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro ⟨hnp, hnq⟩     -- hnp : ¬P, hnq : ¬Q
  intro h               -- h : P ∨ Q（これから矛盾を導く）
  cases h with
  | inl hp => exact hnp hp   -- P ならば ¬P と矛盾
  | inr hq => exact hnq hq   -- Q ならば ¬Q と矛盾

-- ── 分配法則 ──
-- 直感: P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
-- 集合論で言う交差と和集合の分配に相当
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro ⟨hp, hqr⟩      -- hp : P, hqr : Q ∨ R
  cases hqr with
  | inl hq =>           -- Q の場合
    left                -- (P ∧ Q) ∨ (P ∧ R) の左を選ぶ
    exact ⟨hp, hq⟩
  | inr hr =>           -- R の場合
    right               -- (P ∧ Q) ∨ (P ∧ R) の右を選ぶ
    exact ⟨hp, hr⟩

-- ── have を活用した少し長い証明 ──
-- (P → Q) ∧ (Q → R) → (P → R)
-- 直感: 推移律の ∧ バージョン
theorem impl_trans_conj (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) := by
  intro h
  have hpq : P → Q := h.left
  have hqr : Q → R := h.right
  intro hp
  have hq : Q := hpq hp
  have hr : R := hqr hq
  exact hr

-- ── 同値を使った証明 ──
-- (P ↔ Q) → (Q ↔ R) → (P ↔ R)
-- 直感: 同値関係の推移律
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  constructor
  · -- P → R
    intro hp
    have hq : Q := hpq.mp hp     -- .mp = 「→」方向（modus ponens）
    have hr : R := hqr.mp hq
    exact hr
  · -- R → P
    intro hr
    have hq : Q := hqr.mpr hr    -- .mpr = 「←」方向（modus ponens reverse）
    have hp : P := hpq.mpr hq
    exact hp

-- ── 算術と論理の組み合わせ ──
-- 具体的な値で示す
theorem specific_arith : 2 + 3 = 5 ∧ 10 > 7 := by
  constructor
  · omega    -- 2 + 3 = 5
  · omega    -- 10 > 7


-- ////////////////////////////////////////////////////////////
-- まとめ
-- ////////////////////////////////////////////////////////////

/-!
# まとめ: Lean 4 定理証明のポイント

## カリー＝ハワード対応
| 論理               | プログラミング          |
|:-------------------|:----------------------|
| 命題 (Prop)         | 型 (Type)              |
| 証明                | 値/項                  |
| 含意 (→)            | 関数型                 |
| 論理積 (∧)           | 直積型（タプル）         |
| 論理和 (∨)           | 直和型（Either）        |
| ¬P                  | P → Never/Bottom       |
| True                | Unit                   |
| False               | Never/Bottom           |

## 項モード vs タクティクモード
- **項モード**: 証明を式として直接書く。短くて読みやすい。
- **タクティクモード**: `by` 以降でゴールを変形。対話的で分かりやすい。
- 実際にはどちらも混ぜて使う。

## よく使うタクティク一覧
| タクティク    | 用途                                          |
|:------------|:---------------------------------------------|
| intro       | ゴールの `→` や `∀` から仮定を導入              |
| exact       | ゴールにぴったり合う項を渡して完了                |
| apply       | ゴールに定理/関数を逆向きに適用                  |
| rfl         | `x = x` を証明（反射律）                       |
| constructor | ゴールを構造体のサブゴールに分解                  |
| cases       | 仮定を場合分け/分解                             |
| assumption  | 仮定からゴールを自動で見つける                    |
| have        | 中間補題を証明してローカルに追加                  |
| simp        | 自動簡約（登録された補題を使う）                  |
| omega       | 線形算術を自動で解く                             |
| decide      | 決定可能な命題を計算で判定                        |
| induction   | 帰納法（Nat などの帰納型に使う）                  |

## 次のステップ
- Mathlib を探索して、既存の証明を読む
- 帰納法を使ったより複雑な証明に挑戦
- 型クラスと証明の組み合わせ（Verified Programming）
- タクティクの自作（meta programming）
-/

end Tutorial09
