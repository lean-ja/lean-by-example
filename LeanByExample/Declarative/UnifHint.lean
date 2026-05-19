/- # unif_hint

`unif_hint` は、Lean の単一化器(unifier)に追加のヒントを与えるためのコマンドです。

`⊢` の右側に「解きたい単一化問題」を書き、その上に「この問題が来たときに追加する制約」を書きます。
-/

/-- マグマ（集合と二項演算） -/
structure Magma where
  α : Type
  mul : α → α → α

instance : CoeSort Magma Type where
  coe M := M.α

infixl:70 (priority := high) " ** " => Magma.mul _

/-- 自然数上のマグマ -/
def Nat.Magma : Magma where
  α := Nat
  mul a b := a * b

section
  /-
  `S =?= Nat.Magma` が分かったら `S.α =?= Nat` も解けるようにするヒント。
  -/
  local unif_hint (S : Magma) where
    S =?= Nat.Magma
    ⊢ S.α =?= Nat

  -- `S` が推論され、`Nat` 上の演算として解釈される
  #check (3 : Nat) ** (3 : Nat)
end

/-
`local unif_hint` や `scoped unif_hint` の形でも使えます。

`unif_hint` は低レベルかつ強力で、誤ったヒントは単一化を不安定にします。
特に、既存変数をそのまま再利用したヒントは循環してしまうことがあるため、
必要に応じて新しいメタ変数を導入して循環を避けるのが安全です。
-/
