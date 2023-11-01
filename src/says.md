# says

needs: `import Mathlib.Tactic.Says`

[exact?](./exact_question.md) や [apply?](./apply_search.md) は証明を書いている過程で使用することを想定したタクティクです．`Try this: ` という提案をクリックして採用したら，`exact?` や `apply?` は提案内容で上書きされて，最終的な証明には残りません．

では，証明のある部分が `apply?` などにより提案された内容であることを明示したい場合はどうしたら良いでしょうか？`says` タクティクはまさにその問題を解決するタクティクです．

```lean
{{#include ../Examples/Says.lean:first}}
```

また，`simp?` や `aesop?` などに対しても使用することができ，やはりドキュメントとして役に立ちます．

```lean
{{#include ../Examples/Says.lean:aesop}}
```

より詳細には，検索タクティク `X` があり，その提案内容が `Try this: Y` だったとき，`X says` とすると `says` は `Try this: Y` の代わりに `Try this: X says Y` という提案を infoview 上で出します．それをクリックすると，`X says` の内容が `X says Y` で置換されます．そして，`X says Y` が実行されるときには `X` は飛ばされます．

## オプション

* `says.verify : Bool` : `true` にすると，`X says Y` の `Y` のところに，実際には提案されていないタクティクを入れたときにエラーになります．

* `says.no_verify_in_CI : Bool` : `true` にすると，CI 環境で `X says Y` の `Y` の部分が実際に提案されている内容と一致するかのチェックが走らなくなります．
