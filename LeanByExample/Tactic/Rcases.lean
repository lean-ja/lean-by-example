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
  | foo (x y : Nat) : Sample
  | bar (z : String) : Sample

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
