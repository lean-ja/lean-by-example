/- # set_option
`set_option` は、オプションを変更・設定するために使われるコマンドです。

`set_option option_name value` という構文で使用すれば `option_name` という名前のオプションの値を `value` に設定することができます。使用できる `option_name` は [`#help`](#{root}/Diagnostic/Help.md) コマンドまたは [Mathlib4 help](https://seasawher.github.io/mathlib4-help/options/) で確認できます。

有効範囲はその[セクション](#{root}/Declarative/Section.md)の内部またはそのファイルの最後までです。
-/

/-- info: ¬1 + 1 = 2 : Prop -/
#guard_msgs in #check ¬ (1 + 1 = 2)

section

  -- 定義された記法を使わないように設定する
  set_option pp.notation false

  -- 表示される内容が変わった！
  /-- info: Not (Eq (HAdd.hAdd 1 1) 2) : Prop -/
  #guard_msgs in #check ¬ (1 + 1 = 2)

end

-- `section` を抜けると元に戻る
/-- info: ¬1 + 1 = 2 : Prop -/
#guard_msgs in #check ¬ (1 + 1 = 2)
