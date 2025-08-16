/-
# section
`section` は、有効範囲を制限するためのコマンドです。以下に挙げるような効果があります。

* [`variable`](./Variable.md) で定義された引数の有効範囲を制限する。
* [`open`](./Open.md) で開いた名前空間の有効範囲を制限する。
* [`set_option`](./SetOption.md) で設定したオプションの有効範囲を制限する。
* [`local`](#{root}/Modifier/Local.md) で修飾されたコマンドの有効範囲を制限する。

`section` コマンドで開いたセクションは `end` で閉じることができますが、`end` は省略することもできます。`end` を省略した場合はそのファイルの終わりまでが有効範囲となります。

なお以下の例ではセクションの中をインデントしていますが、インデントするのは一般的なコード整形ルールではありません。

以下は `variable` の有効範囲を区切る例です。
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
次は `open` の有効範囲を区切る例です。
-/

section
  open Classical

  -- open されているのでアクセスできる
  #check choice
end

-- `end` 以降は無効になる
#check_failure choice

/- 次は `set_option` の有効範囲を区切る例です。 -/

section
  set_option autoImplicit true

  -- α が暗黙引数になる
  def nilList : List α := []
end

-- `end` 以降は無効になり、α が未定義だというエラーになる
/-⋆-//-- error: Unknown identifier `α` -/
#guard_msgs in --#
def nilList' : List α := []

/- 次は `local` で修飾されたコマンドの有効範囲を区切る例です。-/

section
  -- Nat の inhabited インスタンスを上書きする
  local instance : Inhabited Nat := ⟨1⟩

  -- 上記のインスタンスが有効
  #guard (default : Nat) = 1
end

-- セクションが終わると上記のインスタンスが無効になる
#guard (default : Nat) = 0

/-また、セクションに名前を付けることもできます。名前を付けた場合は、閉じるときにも名前を指定する必要があります。-/

section hoge
  variable (a : Type)

  #check a
end hoge

/- セクションは入れ子にすることもできます。-/

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
