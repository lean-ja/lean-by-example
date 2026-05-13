/- # \#grind_lint

`#grind_lint` コマンドは、[`grind`](#{root}/Tactic/Grind.md) タクティクのために E-マッチングでインスタンス化されるよう登録されたすべての定理を解析するコマンドです。`@[grind]` などの属性で登録された定理が多数の追加インスタンス化を引き起こさないかを検出するために使用します。

ライブラリ開発者が `@[grind]` 属性を定理に付与したとき、その定理が他の定理の大量インスタンス化を連鎖的に引き起こす（いわゆる「インスタンス化の爆発」）かどうかを確認するのに役立ちます。

`#grind_lint` コマンドには以下の 4 つのサブコマンドがあります。

* `inspect`: 特定の定理を個別に詳しく調べます。
* `check`: E-マッチングに登録されたすべての定理を一括してチェックします。
* `mute`: 特定の定理を `#grind_lint` の解析中にインスタンス化されないようにします。
* `skip`: 特定の定理を `#grind_lint check` の解析対象から完全に除外します。

-/

/- ## inspect サブコマンド

`#grind_lint inspect thm₁ …` は、指定した定理を個別に詳しく調べます。

指定した定理のタイプが仮定として与えられた目標 `⊢ False` に対して `grind` を実行し、追加で何個の定理インスタンスが生成されたかを報告します。生成されたインスタンス数がデフォルトの閾値（`min = 10`）を超えた場合にのみ出力が表示されます。
-/

-- `Array.range_succ` は多数の追加インスタンスを引き起こすため、出力される
/-⋆-//--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ
-/
#guard_msgs in --#
#grind_lint inspect Array.range_succ

/- `min` パラメータで出力する閾値を変更できます。`min := 100` とすると、インスタンス数が 100 以下の場合は出力されません。 -/

-- 19 < 100 なので出力されない
#guard_msgs in --#
#grind_lint inspect (min := 100) Array.range_succ

/- 複数の定理を同時に調べることもできます。 -/

/-⋆-//--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: instantiating `Array.range'_succ` triggers 14 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ Array.range'_succ
-/
#guard_msgs in --#
#grind_lint inspect Array.range_succ Array.range'_succ

/- ## check サブコマンド

`#grind_lint check` は、E-マッチングに登録されたすべての定理を一括してチェックします。

`in` キーワードを使うと名前空間でフィルタリングできます。また `in module` とすると、指定したモジュールに属する定理のみをチェックできます。

問題のある定理が見つかった場合は、`#grind_lint inspect <thm>` を追加する「Try this」の提案が表示されます。
-/

-- `Array` 名前空間の定理のうち、インスタンス数が 20 を超えるものをチェックする
#grind_lint check (min := 20) in Array

/- ## mute サブコマンド

`#grind_lint mute thm₁ …` は、指定した定理を `#grind_lint` の解析中にインスタンス化されないようにします（ミュートします）。ミュートされた定理は環境に残り、通常の `grind` タクティクでは引き続き使用されますが、`#grind_lint check` や `#grind_lint inspect` の実行中にはインスタンス化されません。

過剰にインスタンス化を引き起こすような定理が他の定理の解析結果に悪影響を与えている場合、その定理をミュートすることで影響を抑制できます。
-/

-- `Array.getElem_swap` をミュートする
#grind_lint mute Array.getElem_swap

/- ミュートしようとした定理が `@[grind]` 属性によるインスタンス化対象でない場合、エラーになります。 -/

/-⋆-//--
error: `Array.swap_swap` is not marked with the `@[grind]` attribute for theorem instantiation
-/
#guard_msgs in --#
#grind_lint mute Array.swap_swap

/- 同じ定理を 2 回ミュートしようとした場合もエラーになります。 -/

/-⋆-//--
error: `Array.getElem_swap` is already in the `#grind_lint` mute set
-/
#guard_msgs in --#
#grind_lint mute Array.getElem_swap

/- ## skip サブコマンド

`#grind_lint skip thm₁ …` は、指定した定理を `#grind_lint check` の解析対象から完全に除外します。スキップされた定理は `check` 時に報告されませんが、他の定理を解析する際のインスタンス化には引き続き使用されます。これが `mute` との違いです。

`#grind_lint skip suffix name₁ …` とすると、指定したサフィックスで終わる名前を持つすべての定理をスキップできます。
-/

-- `Array.getElem_swap` をスキップする
#grind_lint skip Array.getElem_swap

/- `mute` と同様に、`@[grind]` 属性のない定理をスキップしようとするとエラーになります。 -/

/-⋆-//--
error: `Array.swap_swap` is not marked with the `@[grind]` attribute for theorem instantiation
-/
#guard_msgs in --#
#grind_lint skip Array.swap_swap

/- 同じ定理を 2 回スキップしようとした場合もエラーになります。 -/

/-⋆-//--
error: `Array.getElem_swap` is already in the `#grind_lint` skip set
-/
#guard_msgs in --#
#grind_lint skip Array.getElem_swap

/- `suffix` キーワードを使うと、特定の名前で終わるすべての定理をスキップできます。 -/

-- `succ` で終わる名前を持つすべての定理をスキップする
-- （`Array.range_succ`、`Array.range'_succ` など）
#grind_lint skip suffix succ
