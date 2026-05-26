---
name: lean-article-editing
description: Lean 解説記事を編集・執筆するときに使う。
---

# Lean 記事編集

このスキルは、Lean 解説記事を編集・執筆するときに使う。

## 基本方針

- 記事本文の主張は、具体的な Lean コードで裏付ける。
  - 「できるようになる」と書く場合は、最初はできないという例と、手順後できるようになった例を両方示す。
  - 「エラーになる」と書く場合は、コードによって期待通りにエラーになることを検証する。
- 言葉だけの説明に終始することがないように、コード例による例示を入れる。
- 当たり前の例や人工的な例ではなく、優れた例を使う。
- 外部資料からコード例や記述を拝借する場合は、本文またはコメントに出典を明示する。

## 作業手順

### 1. 下調べ

記事の編集に取り掛かる前に、調査を行う。

1. まず以下の資料を確認する。
   1. [Lean 公式リファレンス](https://lean-lang.org/doc/reference/latest/)
   2. [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
   3. [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
   4. [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
   5. [Lean community blog](https://leanprover-community.github.io/blog/)
   6. [The Hitchhiker's Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025)
   7. [Lean Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
   8. [Tactic Programming Guide](https://github.com/mirefek/lean-tactic-programming-guide)

2. 次に [Lean 公式 ZUlip](https://leanprover.zulipchat.com/) を確認し、示唆的なコード例を探す。

### 2. 編集・執筆

1. 対象記事に対応する `.lean` ファイルを確認する。
2. 本文の主張を拾い、それぞれに対応するコード例があるか確認する。
3. コード例が不足している主張には、短く検証可能な Lean コードを追加する。
4. エラー例は、ファイル全体が失敗しないように `#guard_msgs` や `#check_failure` 等で検証する。
5. 追加・変更したコードを `lake env lean <file>` で検証する。
6. 記事本文と検証用コードの意味の対応が崩れていないか確認する。
7. `A` の記事を新規に追加した場合、既存の `A` への言及は `A` のページへのリンクに置き換える。
8. 最後に、変更内容と検証結果を簡潔に報告する。

### 3. 確認

以下の要件が満たされているか確認する。

- 各記事は、初心者が読んで理解できるように書かれなければいけない。
  仮に必要な予備知識があるとしたら、その予備知識を説明している記事をリンクする。
- 既存の記事構成・用語・文体に合わせることができている。
- コード例で検証されていることしか主張していない。
