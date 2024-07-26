/- # decide
`decide` は、決定可能な命題を示すタクティクです。

命題 `P : Prop` が決定可能であるとは、型クラス [`Decidable`](../Term/TypeClass/Decidable.md) のインスタンスであることを意味します。`P` が `Decidable` のインスタンスであるとき、`decide` 関数を適用することにより `decide P : Bool` が得られるので、これを呼び出すことによって証明したり反証したりすることができます。つまり一言でいえば、決定可能であるとは決定するためのアルゴリズムが存在するということです。
-/
-- 決定可能な命題を決定する関数 decide が存在する
#check (decide : (P : Prop) → [Decidable P] → Bool)

/- [`rfl`](./Rfl.md) タクティクのように、定義からすぐにわかることを示すのに有用なタクティクですが、`rfl` とは異なり反射的でない関係にも使えるほか、間違っている式に使うと「間違っている」と教えてくれることがあります。-/

example : 1 + 2 = 3 := by decide

-- 1 + 1 ≠ 3 は不等式なので rfl では示せないが、decide は示すことができる
example : 1 + 1 ≠ 3 := by
  fail_if_success rfl

  decide

-- 示そうとした式が間違っていると教えてくれた
/--
error: tactic 'decide' proved that the proposition
  1 + 1 = 3
is false
-/
#guard_msgs in example : 1 + 1 = 3 := by decide

/- `decide` は `rfl` の上位互換ではなく、ゴールにローカル変数やメタ変数があると使えません。-/

def double_fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * double_fact n

example (n : Nat) : double_fact (n + 2) = (n + 2) * double_fact n := by
  -- decide は使えない
  fail_if_success decide

  -- rfl は使える
  rfl

/- ## カスタマイズ
`Decidable` 型クラスのインスタンスに登録すれば、自前で用意した述語を `decide` に示させることができます。-/

/-- 奇数であること。Mathlib にある定義とは別に自前で用意 -/
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
