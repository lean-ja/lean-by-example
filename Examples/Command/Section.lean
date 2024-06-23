/-
# section
`section` は，スコープを区切るためのコマンドです．以下のコマンドのスコープを区切ることができます．

* [`variable`](./Variable.md)
* [`open`](./Open.md)
* `set_option`
* `local`

`section` で開いたスコープは `end` で閉じることができますが，省略することもでき，その場合はそのファイルの終わりまでがスコープとなります．

なお以下の例ではセクションの中をインデントしていますが，インデントするのは一般的なコード整形ルールではありません．

次は `variable` のスコープを区切る例です．
-/
set_option autoImplicit false --#

section
  variable (a : Type)

  -- 宣言したので有効
  #check a
end

-- `section` の外に出ると無効になる
#check_failure a

/-
次は `open` のスコープを区切る例です．
-/

section
  open Classical

  -- open されているのでアクセスできる
  #check choice
end

-- スコープが終わると無効になる
#check_failure choice

/- 次は `set_option` のスコープを区切る例です． -/

section
  set_option autoImplicit true

  -- α が暗黙引数になる
  def wrap (x : α) : List α := [x]
end

-- スコープが終わると無効になり，α が未定義だというエラーになる
/--
error: unknown identifier 'α'
---
error: unknown identifier 'α'
-/
#guard_msgs in def wrap' (x : α) : List α := [x]

/- 次は `local` のスコープを区切る例です．`local` は，セクション内部でだけ有効なインスタンスなどを生成します．-/

section
  -- Nat の inhabited インスタンスを上書きする
  local instance : Inhabited Nat := ⟨1⟩

  -- 上記のインスタンスが有効
  #guard (default : Nat) = 1
end

-- スコープが終わると上記のインスタンスが無効になる
#guard (default : Nat) = 0

/-また，セクションに名前を付けることもできます．名前を付けた場合は，閉じるときにも名前を指定する必要があります．-/

section hoge
  variable (a : Type)

  #check a
end hoge

/-! セクションは入れ子にすることもできます．-/

section parent
  variable (a : Type)

  section child
    variable (b : Type)

    -- 親セクションで定義された引数は子セクション内でも有効
    #check a
  end child

  -- child セクションの外なので無効
  #check_failure b
end parent

-- parent セクションの外なので無効
#check_failure a
