/- # Quotient

`Quotient` は、型 `α` 上の同値関係 `r : Setoid α` による **商(quotient)** を表します。[`Setoid`](#{root}/TypeClass/Setoid.md) を受け取って、商型を返します。

## 商とは

商とは、ある二項関係 `r : α → α → Prop` によって同じと見なされるものを同一視したものです。たとえば三角形という図形を考えるとき、回転や平行移動させたものを我々は「同じ形」と認識しますが、これは「回転と平行移動で重なり合う」という二項関係に関する商を取っていることになります。

そもそも「２つのリンゴ」や「２つの消しゴム」といった物の集まりに対して「２個の物の集まりである」という共通点を見出すこと自体、商を取る操作です。この場合は、集合に対して「１対１で漏れのない対応が存在する」という二項関係を考えて商を取ったことになります。したがって、自然数という概念を受け入れた時点で、私たちは商を取るというアイデアを受け入れたことになります。

商がいかに受け入れがたく感じられようと、商は基本的で直観に根ざした操作であると言えます。-/

/- ## Quotient に関する基本的な操作 -/
/-
### Quotient.mk: 同値類を取る操作

型 `α` 上の同値関係 `r : α → α → Prop` があるとき、`r` によって同じと見なされる項同士のグループのことをその項の **同値類(equivalence class)** と呼びます。たとえば、整数全体 `ℤ` において `r x y := 4 ∣ (x - y)` と定義すると `r` は同値関係になりますが、これによる `0` の同値類は `4` で割った余りがゼロになる項の全体、つまり `{0, ±4, ±8, ±12, ..}` という集合になります。

Leanで項 `x : α` に対して、同値関係 `sr : Setoid α` による同値類を取る操作は `Quotient.mk` で表されます。
-/
section --#

variable {α : Type} (sr : Setoid α)

#check (Quotient.mk sr : α → Quotient sr)

end --#
/- 元の型 `α` は、すべての項がどれかの項の同値類に属していて、複数の同値類に属する項はないので、同値類たちの直和として表されます。そこで同値類の全体のことを `α` 上の同値関係 `sr : Setoid α` による **商(quotient)** と呼びます。`Quotient` が表すのは、まさにこの商です。同値類を取る操作 `Quotient.mk` は、商への関数になります。これは恣意的なところがない、構造的に導かれる操作なので、よく **自然な(canonical)** 関数であると形容されます。

商の例を挙げると、たとえば時刻がそうです。時刻は `12` で割った余りで同一視する同値関係が入っていて、`13` 時と `1` 時は同じものだと認識されます。また日付は、時刻を時間・分・秒を無視する同値関係で割ることで得られる商です。
-/

/- ### Quotient.lift: 関数を商へ持ち上げる操作

`α : Type` 上の同値関係 `r : α → α → Prop` と `r` による `α` の商 `α/r` について考えます。ある型 `β` から商 `α/r` への関数を得るには、たとえば自然な関数 `α → α/r` と関数 `β → α` を合成すれば良いですが、商からの関数を得るにはどうすればいいでしょうか？

`α/r` の各要素は同値類であるため、`α` の要素の集まりです。もしも関数 `f : α → β` が、同値類 `as : α/r` のどの要素 `a ∈ as` に対しても同じ値を返すならば、`f` の定義域を `α/r` に持ち上げて `α/r → β` という関数を得ることができます。

理解しにくいと思うのでもう一度別な表現をすると、たとえば２人の人物に対して、そのひとたちの「年齢の和」を考えることはナンセンスです。これは、年齢の和が生まれた年だけによっては決まらず、「今が何年であるか」という情報にも依存してしまうからです。これが、上記で述べた「同値類のどの要素を選ぶかに依存せず同じ値を返す」という前提が成立しない状況の例になっています。逆に、「年齢の差」を考えることはできて、年齢の差を与える関数が作れます。これは、年齢の差がまさに「生年にしか依存しない」からで、生年が同じという同値類で割った商からの関数に持ち上げることができます。

この操作は Lean では `Quotient.lift` で実現できます。もし `α : Type` 上の同値関係 `sr : Setoid α` と関数 `f : α → β` が与えられていて `h : ∀ x, x ≈ y → f x = f y` が成り立つならば、商への持ち上げ `Quotient.lift f h : Quotient sr → β` が得られます。
-/
section --#

variable {α β : Type} (sr : Setoid α)
variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

#check (Quotient.lift f h : Quotient sr → β)

end --#
/- `Quotient.lift` が持ち上げであると言われるのは、元の `f` と値が同じになるからです。つまり、`f' := Quotient.lift f h` としたとき `f' (Quotient.mk x) = f x` が成り立ちます。 -/
section --#

variable {α β : Type} (sr : Setoid α)
variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

example : ∀ x, (Quotient.lift f h) (Quotient.mk sr x) = f x := by
  intro x
  rfl

end --#
/- ### Quotient.inductionOn: 同値類の代表元を取る

同値類 `a : α/r` は、`r` に関して同値な要素の集まりでした。同値類 `a` に対して、その中から一つ要素を選び出すことを **代表元** を取ると言います。「どれを選んでも `r` の意味で同じなので、どれかを取ってその同値類の代表とする」というニュアンスです。

これは Lean では `Quotient.inductionOn` で実現できます。これを使うと、証明の中で「同値類から代表元を取って～」というよくある議論ができます。
-/
section --#

variable {α : Type} (sr : Setoid α)

example (a : Quotient sr) : True := by
  induction a using Quotient.inductionOn with
  | h x =>
    -- `x : α` が得られる
    guard_hyp x : α

    trivial

end --#
/- ### Quotient.sound: 同値なら商へ送って等しい

型 `α` の同値関係 `sr : Setoid α` による商 `α/r` において、`x y : α` が同値つまり `x ≈ y` であるとき、これは商へ送った時には同一視されます。つまり、言い換えれば自然な関数 `Quotient.mk sr : α → α/r` による像が等しくなっているはずです。

この事実には、Lean では `Quotient.sound` という名前が付いています。
-/
section --#

variable {α : Type} (sr : Setoid α)
variable (x y : α) (h : x ≈ y)

/-- 同値なら商へ送って等しい -/
example : Quotient.mk sr x = Quotient.mk sr y := by
  apply Quotient.sound
  exact h

end --#
/- ### Quotient.exact: 商に送って等しいなら同値

`Quotient.sound` とは逆に、商に送って等しいことから同値であることを導く定理には `Quotient.exact` という名前がついています。
-/
section --#

variable {α : Type} (sr : Setoid α)
variable (x y : α)

/-- 商に送って等しいなら同値 -/
example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
  exact Quotient.exact h

end --#
/- ## 使用例 -/
/- ### 順序なしペア

直積型 `A × A` 上の二項関係 `r : A × A → A × A → Prop` を、`r (a₁, a₂) (b₁, b₂) := a₁ = b₁ ∧ a₂ = b₂ ∨ a₁ = b₂ ∧ a₂ = b₁` と定義します。これは、順序を無視してペアを同じと見なす同値関係です。
-/

/-- 順序を無視してペアとして同じかどうか判定する同値関係 -/
@[instance]
def pairRel (A : Type) : Setoid (A × A) where
  r := fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 ∨ p₁.1 = p₂.2 ∧ p₁.2 = p₂.1
  iseqv := by constructor <;> grind

/- この同値関係による商を考えることで、順序なしのペア型を得ることができます。-/

/-- 順序なしペア -/
def UnorderedPair (A : Type) := Quotient (pairRel A)

/- 実際、`(1, 2)` と `(2, 1)` の `UnorderedPair` への像は同じペアとして扱われます。-/

def sample₁ : UnorderedPair Nat := Quotient.mk _ (1, 2)
def sample₂ : UnorderedPair Nat := Quotient.mk _ (2, 1)

example : sample₁ = sample₂ := by
  apply Quotient.sound
  dsimp [(· ≈ ·), pairRel]
  grind

/- ### 自然数の積の商として整数を得る

Lean の標準ライブラリの定義とは異なりますが、`Int` を自然数の積の商として構成することができます。

`Nat × Nat` を考えて、最初の要素を「正の部分」、２つめの要素を「負の部分」と考えるのです。つまり `(a, b) ↦ a - b` という対応を使って整数を構成します。
-/

/-- 自然数を２つペアにしたもの。`(a, b) : PreInt` は `a - b` のつもり -/
abbrev PreInt := Nat × Nat

/- これは全ての整数を表すことができますが、重複があるので整数そのものになりません。この構成だとたとえば `(0, 1)` と `(1, 2)` は同じ整数に対応するので、適切に同一視を入れる必要があります。`(x₁, y₁) : PreInt` と `(x₂, y₂) : PreInt` が同じ整数に対応するのは `x₁ - y₁ = x₂ - y₂` のときですが、これは `x₁ + y₂ = x₂ + y₁` と書き直すことができます。したがって、`PreInt` 上の２項関係 `r` を `x₁ + y₂ = x₂ + y₁` で定義して `r` に関する商を取れば、整数を構成できます。-/

namespace PreInt
  /- ## MyIntのための同値関係の構成 -/

  /-- PreInt 上の二項関係 -/
  def rel (m n : PreInt) : Prop :=
    match m, n with
    | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

  /-- 反射律 -/
  theorem rel.refl : ∀ (m : PreInt), rel m m := by
    intro (m₁, m₂)
    dsimp [rel]
    ac_rfl

  /-- 対称律 -/
  theorem rel.symm : ∀ {m n : PreInt}, rel m n → rel n m := by
    intro (m₁, m₂) (n₁, n₂) h
    dsimp [rel] at *
    omega

  /-- 推移律 -/
  theorem rel.trans : ∀ {l m n : PreInt}, rel l m → rel m n → rel l n := by
    intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
    dsimp [rel] at *
    omega

  /-- `PreInt.rel`は同値関係 -/
  theorem rel.equiv : Equivalence rel :=
    { refl := rel.refl, symm := rel.symm, trans := rel.trans }

  /-- `PreInt` 上の同値関係 -/
  @[instance] def srel : Setoid PreInt := ⟨rel, rel.equiv⟩

end PreInt

/-- 整数の定義 -/
def MyInt := Quotient PreInt.srel

/- `MyInt` 上にマイナス演算 `(- ·) : MyInt → MyInt` を定義しましょう。商からの関数は `lift` で構成することができます。そこでまず `PreInt` 上で関数を実装し、それを持ち上げる方針を取ります。 -/

def PreInt.neg (m : PreInt) : MyInt := match m with
  | (m₁, m₂) => Quotient.mk _ (m₂, m₁)

/-- 整数上のマイナス演算 -/
def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  intro (m₁, m₂) (n₁, n₂) h
  dsimp [PreInt.neg]; apply Quotient.sound
  dsimp [(· ≈ ·), PreInt.srel, PreInt.rel] at *
  omega

instance : Neg MyInt := ⟨MyInt.neg⟩

/- 次に `MyInt` 上に足し算 `(· + ·) : MyInt → MyInt → MyInt` を定義しましょう。商からの関数なのでやはり `Quotient.lift` を使いたくなるのですが、引数が二つあるので `Quotient.lift₂` を使う方が良いです。 -/

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => Quotient.mk _ (m₁ + n₁, m₂ + n₂)

/-- 整数上の足し算 -/
def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m₁', m₂') (n₁', n₂') h₁ h₂
  dsimp [PreInt.add]; apply Quotient.sound
  dsimp [(· ≈ ·), PreInt.srel, PreInt.rel] at *
  omega

instance : Add MyInt := ⟨MyInt.add⟩
