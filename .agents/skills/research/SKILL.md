---
name: research
description: Lean やそのライブラリの機能、構文、タクティク、コード例、仕様、背景理論を調査するときに使用する。
---

# Lean 調査

Lean やそのライブラリの機能、構文、タクティク、コード例、仕様、背景理論を調査するときに使用する。

## 基本方針

- 外部資料を参照した場合は、どこを参照したのか引用元を明示する。
- コード例は、現在のリポジトリの Lean で実行できる形に直す。
- 外部資料の説明やコードをそのまま信用しない。ローカルで具体的なコード例として動くものだけを信用する。

## 手順

1. 以下の公式資料をすべて調査する。
   - [Lean 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
   - [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
   - [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

2. いったん調査報告書を作成する。
   `.agents/tmp` ディレクトリに `research_report_{TIMESTAMP}.lean` というファイルを作成し、そこに調査内容をまとめる。

3. [公式Zulip](https://leanprover.zulipchat.com/) を検索し、関連する話題を調査し、興味深いコード例がないか精査する。

4. 調査報告書を作成する。
   `.agents/tmp` ディレクトリに `zulip_report_{TIMESTAMP}.lean` というファイルを作成し、そこに調査内容をまとめる。
