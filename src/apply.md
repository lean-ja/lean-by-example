# apply

`apply` は含意 `→` をゴールに適用するタクティクです．

ゴールが `⊢ Q` で，ローカルコンテキストに `h: P → Q` があるときに，`apply h` を実行するとゴールが `⊢ P` に書き換わります．

```lean
{{#include ../Examples/Apply.lean:first}}
```

注意点として，`h: P → Q` は `P` の証明を受け取って `Q` の証明を返す関数でもあるので，上記の例は `apply` を使わずに `exact h hP` で閉じることもできます．

```lean
{{#include ../Examples/Apply.lean:exact}}
```

## 否定 ¬ について

また，Lean では否定 `¬ P` は `P → False` として実装されているため，ゴールが `⊢ False` であるときに `hn: ¬P` に対して `apply hn` とするとゴールが `⊢ P` に書き換わります．

```lean
{{#include ../Examples/Apply.lean:not}}
```

## よくあるエラー

`apply` には引数が必須なのですが，省略しても近くにエラーが出ません．一般に，構文的に間違った証明を書いた場合には，エラーがわかりやすい場所に出てくれる保証はありません．

## exact との関連

[exact](./exact.md) の代わりに `apply` を使うことができます．

```lean
{{#include ../Examples/Apply.lean:alt}}
```
