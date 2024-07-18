/- # dsimp

`dsimp` は、定義上(definitionally)等しいような変形だけを行うという制約付きの [`simp`](./Simp.md) で、一言でいえば「名前を定義に展開する」タクティクです。

`dsimp [e₁, e₂, ..., eᵢ]` という構文でゴールに登場する名前 `e₁`, ..., `eᵢ` を定義に展開します。-/
import Lean --#
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

/-- simpConst を良い感じに再帰的に適用して、Expr を単一の Expr.const に簡略化する。-/
def fuse : Expr → Expr
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e => e

/-- fuse は実際に Expr を const に簡略化する。-/
theorem fuse_in_const {e : Expr} : ∃ n, fuse e = .const n := by
  induction e with
  | const n => exists n
  | plus e₁ e₂ ih₁ ih₂ =>
    -- ゴールに fuse が登場する
    guard_target =ₛ ∃ n, fuse (e₁.plus e₂) = const n

    -- fuse を定義に展開する
    dsimp [fuse]
    guard_target =ₛ ∃ n, simpConst (.plus (fuse e₁) (fuse e₂)) = const n

    -- ローカルコンテキストの存在命題を利用してゴールを書き換える
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    rw [ih₁, ih₂]
    guard_target =ₛ ∃ n, simpConst (.plus (const n₁) (const n₂)) = const n

    -- simpConst を定義に展開する
    dsimp [simpConst]
    guard_target =ₛ ∃ n, const (n₁ + n₂) = const n

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
「定義上等しいような変形だけを行う」というのは、`rfl` で示せるような命題だけを使用するという意味です。`rfl` で示せないような簡約は `dsimp` ではできません。-/

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

/-- ゼロを左から足しても変わらない。
自明なようだが、MyNat.add は m に対する場合分けで定義されているので定義上明らかではない。-/
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

/- ## unfold との違い
同じく名前を定義に展開するタクティクとして [`unfold`](./Unfold.md) があります。たいていの場合両者は同じように使うことができますが、`unfold` は次のような意外な挙動をすることがあるので `dsimp` を使うことを推奨します。
-/

-- α の部分集合を表す型
def Set (α : Type) := α → Prop

-- 部分集合の共通部分を取る操作
def Set.inter {α : Type} (s t : Set α) : Set α := fun x => s x ∧ t x

-- ∩ という記法を使えるようにする
instance (α : Type) : Inter (Set α) where
  inter := Set.inter

variable {α : Type} (s u : Set α)

example: True ∨ (s ∩ u = u ∩ s) := by
  -- ∩ 記号を展開する
  dsimp [Inter.inter]

  -- Set.inter で書き直される
  guard_target =ₛ True ∨ (s.inter u = u.inter s)

  left; trivial

example : True ∨ (s ∩ u = u ∩ s) := by
  -- ∩ 記号を展開する
  unfold Inter.inter

  -- 展開結果にインスタンスが入ってしまう
  show True ∨ (instInterSet α).1 s u = (instInterSet α).1 u s

  -- 再びインスタンスの展開を試みると
  unfold instInterSet

  -- 振り出しに戻ってしまう！
  show True ∨ (s ∩ u = u ∩ s)

  left; trivial

/- また、`dsimp` は識別子(`ident`)ではないものに対しても簡約を行うことができますが、`unfold` は識別子でなければ簡約が行えません。これも `dsimp` の長所といえます。-/

example : True ∨ (s ∩ u = u ∩ s) := by
  -- dsimp はラムダ式に対する簡約ができる
  dsimp [(· ∩ ·)]

  -- ゴールが展開される
  guard_target =ₛ True ∨ (s.inter u = u.inter s)

  left; trivial

open Lean Parser

/-- parse できるかどうかチェックする関数 -/
def checkParse (cat : Name) (s : String) : MetaM Unit := do
  if let .error s := runParserCategory (← getEnv) cat s then
    throwError s

-- 識別子を渡したときはパースできる
run_meta checkParse `tactic "unfold Inter.inter"

-- 識別子でないものを渡すとパースできない
/-- error: <input>:1:7: expected identifier -/
#guard_msgs in
run_meta checkParse `tactic "unfold (· ∩ ·)"
