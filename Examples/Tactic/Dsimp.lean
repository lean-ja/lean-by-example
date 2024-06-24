/- # dsimp

`dsimp` は，定義上(definitionally)等しいような変形だけを行うという制約付きの [`simp`](./Simp.md) で，一言でいえば「名前を定義に展開する」タクティクです．

`dsimp [e₁, e₂, ..., eᵢ]` という構文でゴールに登場する名前 `e₁`, ..., `eᵢ` を定義に展開します．-/

/-- 算術式 -/
inductive Expr where
  | const : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

open Expr

/-- サイズ２の Expr を計算によって簡略化する -/
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂) => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e => e

/-- simpConst を良い感じに再帰的に適用して，Expr を単一の Expr.const に簡略化する.-/
def fuse : Expr → Expr
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e => e

/-- fuse は実際に Expr を const に簡略化する. -/
theorem fuse_in_const {e : Expr} : ∃ n, fuse e = .const n := by
  induction e with
  | const n => exists n
  | plus e₁ e₂ ih₁ ih₂ =>
    -- ゴールに fuse が登場する
    show ∃ n, fuse (e₁.plus e₂) = const n

    -- fuse を定義に展開する
    dsimp [fuse]
    show ∃ n, simpConst (.plus (fuse e₁) (fuse e₂)) = const n

    -- ローカルコンテキストの存在命題を利用してゴールを書き換える
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    rw [ih₁, ih₂]
    show ∃ n, simpConst (.plus (const n₁) (const n₂)) = const n

    -- simpConst を定義に展開する
    dsimp [simpConst]
    show ∃ n, const (n₁ + n₂) = const n

    -- n = n₁ + n₂ とすれば良い
    exists n₁ + n₂
  | times e₁ e₂ ih₁ ih₂ =>
    -- plus の場合と同様
    dsimp [fuse, simpConst]
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    rw [ih₁, ih₂]
    exists n₁ * n₂

/- ## 舞台裏
「定義上等しいような変形だけを行う」というのは，`rfl` で示せるような命題だけを使用するという意味です．`rfl` で示せないような簡約は `dsimp` ではできません．-/

/-- 自前で定義した自然数 -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-- MyNat の足し算 -/
def MyNat.add (n m : MyNat) : MyNat :=
  match m with
  | MyNat.zero => n
  | MyNat.succ m => MyNat.succ (MyNat.add n m)

/-- MyNat.add を足し算記号で書けるようにする -/
infix:65 " + " => MyNat.add

/-- ゼロを左から足しても変わらない．
自明なようだが，MyNat.add は m に対する場合分けで定義されているので定義上明らかではない. -/
theorem MyNat.zero_add {n : MyNat} : MyNat.zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [MyNat.add]
    rw [ih]

example (n : MyNat) : n + MyNat.zero = n := by
  -- rfl で証明ができる
  try rfl; done; fail

  -- dsimp でも証明ができる
  dsimp [MyNat.add]

example (n : MyNat) : MyNat.zero + n = n := by
  -- rfl では証明ができない
  fail_if_success rfl

  -- dsimp でも証明ができない
  fail_if_success dsimp [MyNat.add]

  rw [MyNat.zero_add]
