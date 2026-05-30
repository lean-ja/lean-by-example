---
name: research
description: Lean/Mathlib の機能、構文、タクティク、コード例、仕様、出典、背景理論を調査するときに使用する。Lean by Example の記事追加・編集前の下調べ、既存記事の根拠確認、外部資料からのコード例収集、Lean のバージョン差の確認で使う。
---

# Lean 調査

Lean by Example の記事追加・編集に必要な下調べを行う。調査結果は、記事本文で使える具体的な Lean コード例と、確認可能な出典に落とし込む。

## 基本方針

- 一次情報を優先する。Lean/Mathlib の実装、公式ドキュメント、公式書籍、Mathlib ドキュメントを先に確認する。
- コード例は、現在のリポジトリの Lean で実行できる形に直す。`lean-toolchain` と `lake-manifest.json` の依存関係を前提にする。
- 外部資料の説明やコードをそのまま信用しない。最終的にはローカルの Lean で検証する。
- Zulip、ブログ、GitHub issue、PR はヒントとして扱う。記事に採用する前に、公式資料または実装で裏を取る。
- 調査対象が Lean のバージョンに依存しそうな場合は、対象バージョンを明記する。
- 引用・翻案・コードの由来がある場合は、記事本文またはコメントに出典を残す。

## 調査手順

1. まず調査したい語をリポジトリ内で探す。
   ```powershell
   rg "keyword" LeanByExample
   ```

2. 既存記事と似たテーマがある場合は、その `.lean` ファイルの構成、用語、検証方法を確認する。

3. 依存パッケージが取得済みなら、Lean/Mathlib のソースも検索する。
   ```powershell
   rg "keyword" .lake\packages
   ```

4. 以下の外部資料をすべて確認する。
   - [Lean 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
   - [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
   - [Mathlib ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
   - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
   - [Lean Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
   - [Lean community blog](https://leanprover-community.github.io/blog/)
   - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
   - [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
   - [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025)
   - [Lean Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
   - [Tactic Programming Guide](https://github.com/mirefek/lean-tactic-programming-guide)
   - [Lean 公式 ZUlip](https://leanprover.zulipchat.com/)

5. 候補となる説明・コード例・反例を短くメモする。最低限、次を残す。
   - 何を説明するための例か
   - 出典 URL またはローカルファイルパス
   - そのまま使えるか、記事向けに単純化が必要か
   - 現在の Lean で検証済みか

## コード例の作り方

- 記事で示す主張ごとに、最小だが人工的すぎないコード例を用意する。
- 成功例だけでなく、誤用や失敗例が理解に必要なら `#guard_msgs`、`#check_failure`、`#guard` などで失敗も検証する。
- 型や展開結果を調べるときは `#check`、`#print`、`#reduce`、`#eval`、`#synth`、`#instances` を使う。
- タクティクの記事では、最終証明だけでなく「どのゴールがどう変わるか」を説明できる例を探す。
- Mathlib の例を借りる場合は、初心者向け記事として不要な一般化・重い前提・長い証明を削る。
- `sorry` を含む例は、未完成例として明示する場合を除き採用しない。

## 検証

1. 既存記事を編集する場合は対象 `.lean` ファイルで検証する。
   ```powershell
   lake env lean LeanByExample\Path\To\File.lean
   ```

2. 調査用の一時コードが必要な場合は、最終的に記事へ移すか削除する。不要な調査ファイルを残さない。

3. 複数ファイルに影響する変更や import の追加がある場合は、必要に応じて `lake build` を実行する。

4. エラーや警告を記事で扱う場合は、実際のメッセージが現在の Lean で再現することを確認する。

## 調査結果のまとめ方

調査結果を報告書 `REPORT_TEMP.md` にまとめる。
報告書は 3000 行以内にまとめる。

報告や次工程への引き継ぎでは、次を簡潔に示す。

- 調査対象
- 確認した主な出典
- 採用できそうなコード例
- 現在の Lean で検証した内容
- 未確認の点、またはバージョン差に注意が必要な点
