/- # set_option
`set_option` は、オプションを変更・設定するために使われるコマンドです。

`set_option option_name value` という構文で使用すれば `option_name` という名前のオプションの値を `value` に設定することができます。使用できる `option_name` は [`#help`](#{root}/Diagnostic/Help.md) コマンドで確認できます。

有効範囲はその[セクション](./Section.md)の内部またはそのファイルの最後までです。
-/

-- P は命題
variable (P : Prop)

/-- info: ¬P : Prop -/
#guard_msgs in #check ¬ P

-- 定義された記法を使わないように設定する
set_option pp.notation false

-- 表示される内容が変わった！
/-- info: Not P : Prop -/
#guard_msgs in #check ¬ P
