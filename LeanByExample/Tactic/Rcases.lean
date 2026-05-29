/- # rcases

`rcases` は [`cases`](./Cases.md) をパターンに従って再帰的(recursive)に適用します。`cases` の上位互換という立ち位置です。-/

variable (P Q R : Prop)

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  -- 場合分けをする
  rcases h with hP | hQ
  · apply hPR hP
  · apply hQR hQ

-- 論理積 ∧ に対しても使える
example : P ∧ Q → Q ∧ P := by
  -- `h: P ∧ Q` と仮定する
  intro h

  -- `h: P ∧ Q` を `hP: P` と `hQ: Q` に分解する
  rcases h with ⟨hP, hQ⟩

  -- `Q ∧ P` を証明する
  exact ⟨hQ, hP⟩

/- `rcases` は一般には `⟨x₁, x₂, ...⟩ | ⟨y₁, y₂, ...⟩ | ...` という記法で[帰納型](#{root}/Declarative/Inductive.md)の分解が可能です。-/

inductive Sample where
  | foo (x y : Nat)
  | bar (z : String)

example (s : Sample) : True := by
  rcases s with ⟨x, y⟩ | ⟨z⟩

  case foo =>
    -- `x`, `y` が取り出せている
    guard_hyp x : Nat
    guard_hyp y : Nat

    trivial

  case bar =>
    -- `z` が取り出せている
    guard_hyp z : String

    trivial

/- ## rfl パターン

`rcases` のパターンには `rfl` も使えます。等式の仮定 `h : a = b` に対して `rcases h with rfl` と書くと、`b` が `a` に書き変わります。つまり、`rw` タクティクで書き換える手間が省けます。
-/

example {a b c : Nat} (h : a = b) : a + c = b + c := by
  rcases h with rfl

  -- `b` が `a` に書き変わる
  guard_target =ₛ a + c = a + c

  rfl

example {a b : Nat} (h : a = b ∧ b = 3) : a = 3 := by
  rcases h with ⟨rfl, hb⟩

  -- `b` が `a` に書き変わる
  guard_target =ₛ a = 3

  exact hb
