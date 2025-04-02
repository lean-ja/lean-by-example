/- # dsimp

`dsimp` は、定義上(definitionally)等しいような変形だけを行うという制約付きの [`simp`](./Simp.md) で、一言でいえば「名前を定義に展開する」タクティクです。

`dsimp [e₁, e₂, ..., eᵢ]` という構文でゴールに登場する名前 `e₁, ..., eᵢ` を定義に展開します。-/
import Lean --#

/-- `n < m`を真似て構成した自前の述語 -/
def Nat.mylt (n m : Nat) := (n + 1) ≤ m

/-- `n < m`と書いたら標準の`Nat.lt`の代わりに上記の`Nat.mylt`を使用する -/
instance : LT Nat where
  lt := Nat.mylt

example : 1 < 2 := by
  -- `<`という記号、およびその実装である`Nat.mylt`を展開する
  dsimp [(· < ·), Nat.mylt]

  -- ゴールが展開されて変形された
  guard_target =ₛ 2 ≤ 2

  omega

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
  rfl

example (n : MyNat) : n + MyNat.zero = n := by
  -- dsimp でも証明ができる
  dsimp [MyNat.add]

example (n : MyNat) : MyNat.zero + n = n := by
  -- rfl では証明ができない
  fail_if_success rfl

  -- dsimp でも証明ができない
  fail_if_success dsimp [MyNat.add]

  rw [MyNat.zero_add]

/- ## unfold と比べた長所
同じく名前を定義に展開するタクティクとして [`unfold`](./Unfold.md) があります。たいていの場合両者は同じように使うことができますが、`unfold` は次のような意外な挙動をすることがあります。
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

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- 識別子を渡したときはパースできる
#eval parse `tactic "unfold Inter.inter"

-- 識別子でないものを渡すとパースできない
/-⋆-//-- error: <input>:1:7: expected identifier -/
#guard_msgs in --#
#eval parse `tactic "unfold (· ∩ ·)"
