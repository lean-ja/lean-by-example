/- # grind

`grind` は、現代の SMT ソルバにインスパイアされた証明自動化タクティクです。

## grind の動作原理

### 合同閉包(congruence closure)

`grind` の中核には、合同閉包(congruence closure)アルゴリズムが使用されています。これは、黒板に「今まで分かったこと」を蓄積していくところをイメージすると分かりやすいかもしれません。

`grind` は新しい等式や不等式を発見するたびに、その事実を黒板に書き込んでいきます。そして、「互いに等しいと分かっているグループ」を同値類(equivalence classes)としてまとめて管理します。

`grind` は合同性(congruence)つまり `a₁ = a₂` ならば `f a₁ = f a₂` が成り立つことを認識しているので、そういったパターンを見つけると黒板に書き込んでいきます。
-/
section --#
variable {α : Type} (a₁ a₂ : α)

set_option trace.grind.debug.congr true

/-⋆-//--
trace: [grind.debug.congr] f a₂ = f a₁
[grind.debug.congr] f (f a₂) = f (f a₁)
-/
#guard_msgs in --#
example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

end --#
/- ### ケース分割

`grind` は `match` 式や `if` 式を場合分けして分解することができます。
-/

def oneOrTwoIf (n : Nat) : Nat :=
  if n = 0 then 1 else 2

example (n : Nat) : oneOrTwoIf n > 0 := by
  dsimp [oneOrTwoIf]
  grind

def oneOrTwoMatch (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2

-- どういうケース分割を行ったかトレースを出す
set_option trace.grind.split true in

/-⋆-//--
trace: [grind.split] match n with
    | 0 => 1
    | x => 2, generation: 0
-/
#guard_msgs in --#
example (n : Nat) : oneOrTwoMatch n > 0 := by
  dsimp [oneOrTwoMatch]
  grind

/- `[grind cases]` 属性が付与されている帰納的命題命題に対しても、ケース分割を行います。 -/

inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : ∀ n, Even n → Even (n + 2)

example : ¬ Even 1 := by
  -- まだ示せない
  fail_if_success grind

  -- grind なしで証明する
  intro h
  cases h

-- 属性を付与する
attribute [grind cases] Even

example : ¬ Even 1 := by
  -- grind で示せるようになった
  grind
