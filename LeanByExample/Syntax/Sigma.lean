/- # Σ

`Σ` は、**依存ペア型(dependent pair type)** を表します。`α : Type u` という添え字族によって添え字付けられた型の族 `β : α → Type v` があるとき、`Σ (a : α), β a` は `α` の要素とそれに対応する `β a` の要素のペアの型を表します。
-/

/-
たとえば、`[(Nat, 1), (String, "hello"), (Bool, true)]` というようなリストを考えてみます。
このリストに正しく型を付けるにはどうすればいいでしょうか？
通常の直積型では、「右の要素の型が左の要素の型に依存する」ことが許されないので、型を付けることができません。
-/

#check_failure [(Nat, 1), (String, "hello"), (Bool, true)]

/- しかし、依存ペア型を使うことで解決できます。
この場合、リストの中身の型は `Σ (α : Type), α` になります。
これは、`(α : Type) × α` と同じ意味です。
-/

example : (Σ (α : Type), α) = ((α : Type) × α) := by rfl

/- これを使うと、次のようにリストに型を付けることができます。 -/

def sample : List ((α : Type) × α) :=
  [⟨Nat, 1⟩, ⟨String, "hello"⟩, ⟨Bool, true⟩]

/-
## 依存和型

依存ペア型は、**依存和型(dependent sum type)** とも呼ばれます。

これは一見すると奇妙に見えます。`(a : α) × β a` という表記から見ると、掛け算(`×`)のように見えるからです。

しかし、依存ペア型がどのような関数の **図式(diagram)** の中にいるのかを考えると、（つまり周辺の関数を見ると）和との類似が見えてきます。依存型ではない、ただの和型 `A ⊕ B` を考えると、この型への自然な関数 `inl : A → A ⊕ B` と `inr : B → A ⊕ B` が存在し、これは単射です。
-/

variable {A B : Type}

example : (Sum.inl : A → A ⊕ B).Injective := by
  intro a1 a2 h
  simp_all

example : (Sum.inr : B → A ⊕ B).Injective := by
  intro b1 b2 h
  simp_all

/-
依存ペア型についても同様に、各構成要素からの自然な関数が存在します。添え字族 `α : Type u` と型の族 `β : α → Type v` があるとき、各構成要素 `β a` からの自然な関数 `β a → (a : α) × β a` が存在して、これは単射です。
-/

/-- 依存和型への、各構成要素からの自然な関数 -/
def Sigma.inj {α : Type u} (β : α → Type v) (x : α) : β x → (a : α) × β a :=
  fun b => ⟨x, b⟩

/-- 自然な関数 `Sigma.inj β x` はすべての `x : α` に対して単射 -/
example {α : Type u} (β : α → Type v) (x : α) : (Sigma.inj β x).Injective := by
  intro b1 b2 h
  simpa [Sigma.inj] using h

/-
このように周辺の関数との関係を見ると、依存ペア型はペア(積)ではなくて和のように振る舞っていることがわかります。
-/
