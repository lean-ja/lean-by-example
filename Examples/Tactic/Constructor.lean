/- # constructor

`constructor` はゴールを分割するためのタクティクです．

たとえばゴールが `⊢ P ∧ Q` であるとき，`constructor` を実行すると，ゴールが２つのサブゴール `⊢ P` と `⊢ Q` に分割されます．-/
variable (P Q : Prop)

example (hP: P) (hQ: Q) : P ∧ Q := by
  -- goal が `left` と `right` に分割される
  constructor

  case left =>
    -- `P` を示す
    show P
    exact hP

  case right =>
    -- `Q` を示す
    show Q
    exact hQ

/- またゴールが同値 `P ↔ Q` であるとき，`constructor` を実行するとゴールが２つのサブゴール `⊢ P → Q` と `Q → P` に分割されます．-/

example (x : Nat) : x = 0 ↔ x + 1 = 1 := by
  constructor
  case mp =>
    -- `x = 0 → x + 1 = 1` を示す
    show x = 0 → x + 1 = 1
    intro hx
    rw [hx]
  case mpr =>
    -- `x + 1 = 1 → x = 0` を示す
    show x + 1 = 1 → x = 0
    simp_all

/- ## 補足
このように，`constructor` は論理積 `∧` や同値 `↔` を「示す」ために使われます．逆にこういった命題が仮定にあって「使用したい」場合は [`obtain`](./Obtain.md) や [`have`](./Have.md) などが使用できます．-/

example (h: P ∧ Q) : P := by
  obtain ⟨hp, hq⟩ := h
  exact hp

example (h : P ↔ Q) (hP : P) : Q := by
  have ⟨pq, qp⟩ := h
  apply pq
  assumption

/- また論理積や同値性は構造体なので，次の関数も利用できます．-/

-- 論理積から構成要素を取り出す関数
#check (And.left : P ∧ Q → P)
#check (And.right : P ∧ Q → Q)

-- 同値から構成要素を取り出す関数
#check (Iff.mp : (P ↔ Q) → P → Q)
#check (Iff.mpr : (P ↔ Q) → Q → P)

/- ## 舞台裏
`constructor` は一般に，論理積や同値に限らずゴールにある任意の構造体を分解することができます．
-/

structure Sample where
  name : String
  index : Nat

def getSample (index : Nat) (name : String) : Sample := by
  -- constructor タクティクでゴールの構造体をフィールドに分解する
  constructor

  · exact name
  · exact index
