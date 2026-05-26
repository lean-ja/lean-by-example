/- # decide
`decide` は、決定可能な命題を示すタクティクです。

命題 `P : Prop` が決定可能であるとは、型クラス [`Decidable`](#{root}/TypeClass/Decidable.md) のインスタンスであることを意味します。`P` が `Decidable` のインスタンスであるとき、`decide` 関数を適用することにより `decide P : Bool` が得られるので、これを使って証明したり反証したりできます。
-/

-- 決定可能な命題を決定する関数 decide が存在する
#check (decide : (P : Prop) → [Decidable P] → Bool)

/-
つまり一言で言えば、`decide` とは「計算すればわかる」ことを証明または反証するためのタクティクです。
-/

-- 計算すればわかるので示せる
example : 1 + 1 = 2 := by decide

-- 等式以外でも、決定可能なら示せる
example : 5 * 7 ≤ 21 + 19 := by decide

-- 整除関係も決定可能なので示せる
example : 11 ∣ 121 := by decide

-- 証明しようとしたことが間違っていたら教えてくれる
/-⋆-//--
error: Tactic `decide` proved that the proposition
  15 ∣ 21
is false
-/
#guard_msgs in --#
example : 15 ∣ 21 := by decide

/- ## カスタマイズ

`Decidable` 型クラスのインスタンスに登録すれば、自前で用意した述語を `decide` に示させることができます。-/

/-- 奇数であること -/
def Odd (n : Int) : Prop := ∃ t : Int, n = 2 * t + 1

example : Odd (7 : Int) := by
  -- 自前で定義したばかりなので decide で示せない
  fail_if_success decide

  -- 手動で示す
  exists 3

/-- 奇数であることが決定可能であること -/
instance (n : Int) : Decidable (Odd n) := by
  -- n % 2 の計算に帰着させる
  refine decidable_of_iff (n % 2 = 1) ?_
  dsimp [Odd]
  constructor <;> intro h
  · exists (n / 2)
    omega
  · obtain ⟨t, th⟩ := h
    rw [th]
    omega

-- decide で証明できる
-- 具体的に 7 = 2 * k + 1 となる k を求める必要がなくなって嬉しい
theorem odd_seven : Odd (7 : Int) := by
  decide

/- ## よくあるエラー

`decide` は、[整礎再帰](#{root}/Modifier/TerminationBy.md) を使って定義された関数に対してはそのまま使用することができません。[`native_decide`](#{root}/Tactic/NativeDecide.md) タクティクを使えば一応証明は可能です。
-/

/-- 文字列を指定した長さになるまで特定の文字で埋める関数 -/
def String.padWith (s : String) (c : Char) (n : Nat) : String :=
  if n ≤ s.length then
    s
  else
    (c.toString ++ s).padWith c n
termination_by n - s.length

#guard String.padWith "abc" 'x' 5 = "xxabc"

example : String.padWith "abc" 'x' 5 = "xxabc" := by
  -- decide は整礎再帰の関数には使えない
  fail_if_success decide

  -- 一応証明できる
  native_decide
