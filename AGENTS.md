# codex と copilot 向けの指示

## 環境構築

以下のコマンドで elan をインストールし、その後PATHを通してください。

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

## 記事の編集方針

1. 記述はすべて、具体的なコードによって例示され、裏付けられるべきです。
  1. 「～ができるようになる」ことを本文に書くのであれば、「最初は~ができない」ことと、「しかるべき手順の後～ができるようになる」ことの両方をコードで示すべきです。
  2. 「～をするとエラーになる」ことを本文に書くのであれば、エラーになることをエラーなしに検証するコードを示すべきです。
2. 以下を主に情報源としてください。他の情報源を使用しても構いません。
   1. 公式リファレンス https://lean-lang.org/doc/reference/latest/
   2. https://lean-lang.org/functional_programming_in_lean/
   3. https://leanprover-community.github.io/mathematics_in_lean/
   4. https://lean-lang.org/theorem_proving_in_lean4/
   5. 公式Zulip https://leanprover.zulipchat.com/
3. 非自明なコード例を使用する際は、どこが出典であるかを明示し、正しく引用してください。
