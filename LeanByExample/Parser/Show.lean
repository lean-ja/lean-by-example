/- # show .. from

`show T from e` は、型 `T` の項 `e` を表す構文です。項に対して型 `T` を明示することができます。
-/

-- とても単純な使用例
#check show Nat from 1

-- `#eval` コマンドに式を渡す際に、期待される型を明示するために show を用いている例
#eval show IO Unit from do
  IO.println "Hello, world!"
  IO.println "Goodbye, world!"

/- また、Lean においては命題 `P : Prop` は型なので、命題 `P` の証明を `show P from by ...` の形で構成することができます。これを利用すると、名前を付けずに補題を引用することができます。-/

example (n m : Nat) (h : n = m) : (n + 0) + m = m + m := by
  -- `n + 0 = n` という補題をその場で証明して利用している
  rw [show n + 0 = n from by simp]

  rw [h]

/- よく似た構文を持つものとして、[`show`](#{root}/Tactic/Show.md) タクティクがあります。-/
