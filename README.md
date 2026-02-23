# lean-lang-sandbox

Lean 4 の学習用サンドボックス。定理証明からプログラミングまで、段階的に学べるチュートリアル集。

## セットアップ

```bash
# elan (Lean バージョンマネージャ) をインストール
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:stable

# PATH を通す
export PATH="$HOME/.elan/bin:$PATH"

# ビルド
lake build

# 実行
lake exe lean-lang-sandbox
```

## チュートリアル一覧

`LeanLangSandbox/` 配下に、01 から順に読むことを想定したチュートリアルがあります。
すべて日本語コメント付き、`#eval` で結果を確認できます。

| # | ファイル | テーマ | 内容 |
|---|---|---|---|
| 01 | `Tutorial01_Basics.lean` | 基本型・演算 | Nat, Int, Float, String, Bool, Char, let, #eval, #check |
| 02 | `Tutorial02_Functions.lean` | 関数 | def, fun, カリー化, 部分適用, where, 再帰, 停止性証明 |
| 03 | `Tutorial03_PatternMatch.lean` | パターンマッチ | match, ワイルドカード, ガード, 網羅性, 電卓の実装 |
| 04 | `Tutorial04_Lists.lean` | リスト操作 | List, map, filter, fold, Option, 再帰関数 |
| 05 | `Tutorial05_Structures.lean` | 構造体 | structure, ドット記法, with 更新, メソッド, deriving |
| 06 | `Tutorial06_Inductive.lean` | 帰納型 (ADT) | enum, 再帰型, 二分木, 式の木, JSON型 |
| 07 | `Tutorial07_TypeClasses.lean` | 型クラス | class, instance, ToString, BEq, Ord, deriving |
| 08 | `Tutorial08_IO.lean` | IO・do記法 | IO モナド, do, for, while, try/catch, CLI |
| 09 | `Tutorial09_Proofs.lean` | 定理証明入門 | Prop, theorem, tactics (intro, exact, simp, omega, decide) |
| 10 | `Tutorial10_DependentTypes.lean` | 依存型 | Vect, Fin, Subtype, 状態マシン, コンパイル時安全性 |

## その他のファイル

| ファイル | 内容 |
|---|---|
| `Basic.lean` | 定理証明のデモ (P→P, AND交換, 対偶, safeHead) |
| `FizzBuzz.lean` | FizzBuzz + その性質の証明 |
| `Main.lean` | エントリポイント (FizzBuzz 実行) |

## Lean 4 の核心

**「コンパイルが通る = 証明が正しい」**

Lean は定理証明とプログラミングが同じ言語で書ける。命題は型、証明はプログラム。

## 環境

- Lean 4.28.0
- Lake 5.0.0
