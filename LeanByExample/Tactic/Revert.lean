/- # revert

`revert` は、[`intro`](#{root}/Tactic/Intro.md) の逆の操作をするタクティクです。ゴールが `⊢ P` であるときに `revert x` を実行すると、ゴールが `∀ x, P` に変わります。
-/

#guard_msgs (drop warning) in --#
example (x : Nat) : x = 1 := by
  revert x

  -- ゴールが `∀ x, x = 1` に変わる
  guard_target =ₛ ∀ x, x = 1

  sorry

/- ## 用途

`revert` には一見使い道がないようですが、識別子をマクロ内で導入するのを避けたいときに役に立ちます。

たとえば次のように自然数の商として整数を定義したとしましょう。
-/

def PreInt := Nat × Nat

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

namespace PreInt
  /- ## PreInt.rは同値関係である -/

  /-- 反射律 -/
  theorem r.refl : ∀ (m : PreInt), r m m := by
    intro (m₁, m₂)
    dsimp [r]
    ac_rfl

  /-- 対称律 -/
  theorem r.symm : ∀ {m n : PreInt}, r m n → r n m := by
    intro (m₁, m₂) (n₁, n₂) h
    dsimp [r] at *
    omega

  /-- 推移律 -/
  theorem r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
    intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
    dsimp [r] at *
    omega

  /-- `PreInt.r`は同値関係 -/
  theorem r.equiv : Equivalence r :=
    { refl := r.refl, symm := r.symm, trans := r.trans }

end PreInt

/-- `PreInt`上の同値関係 -/
@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩

/-- 整数。`Nat × Nat`を同値関係で割ることで構成している。 -/
@[reducible] def MyInt := Quotient PreInt.sr

namespace MyInt
  /- ## MyInt を数値リテラルで表せるようにする -/

  /-- 同値類を表す記法 -/
  notation:arg (priority := low) "⟦" a "⟧" => Quotient.mk _ a

  def ofNat (n : Nat) : MyInt := ⟦(n, 0)⟧

  instance {n : Nat} : OfNat MyInt n where
    ofNat := MyInt.ofNat n

end MyInt
/- このとき、整数上の足し算を次のように構成することができます。 -/

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

/-- 整数の足し算 -/
def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
  dsimp [PreInt.add]
  apply Quotient.sound
  dsimp [(· ≈ ·), Setoid.r, PreInt.r] at *
  omega

instance : Add MyInt where
  add := MyInt.add

/- ここで `m + 0 = m` と `0 + m = m` の証明は次のように書けます。-/

example (m : MyInt) : m + 0 = m := by
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quot.sound
  dsimp [(· ≈ ·), Setoid.r, PreInt.r] at *
  omega

example (m : MyInt) : 0 + m = m := by
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quot.sound
  dsimp [(· ≈ ·), Setoid.r, PreInt.r] at *
  omega

/- 2つの証明はまったく同じです！そこで証明を共通化すべくマクロを定義してみると、素朴には上手くいきません。 -/
section
  local macro "unfold_int" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a₁, a₂)
    apply Quot.sound
    dsimp [(· ≈ ·), Setoid.r, PreInt.r] at *
    omega
  )

  #guard_msgs (drop warning) in --#
  example (m : MyInt) : m + 0 = m := by
    -- 証明が通らない！
    fail_if_success unfold_int
    sorry
end
/- なぜ上手くいかないかというと、マクロ内で参照している`m`という識別子がLeanのマクロ衛生機構に引っかかって使用不可になってしまうからです。仮に引っかからなかったとしても、証明すべき命題の変数が`m`ではなかったらどうするのでしょうか？このままではこのマクロは使い物になりません。

この問題を解決する方法の一つが、`revert` を使って自由変数を消してしまうことです。
-/
section
  local macro "unfold_int" : tactic => `(tactic| focus
    intro m
    refine Quotient.inductionOn m ?_
    intro (a₁, a₂)
    apply Quot.sound
    dsimp [(· ≈ ·), Setoid.r, PreInt.r] at *
    omega
  )

  example (m : MyInt) : m + 0 = m := by
    revert m
    unfold_int

  example (m : MyInt) : 0 + m = m := by
    revert m
    unfold_int
end
