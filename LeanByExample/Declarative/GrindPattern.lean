/- # grind_pattern

`grind_pattern` コマンドは、定理を [`grind`](#{root}/Tactic/Grind.md) タクティクに再利用させるためのパターンを指定するためのコマンドです。
-/

/-- 何らかの二項関係 -/
opaque R : Nat → Nat → Prop

/-- R は推移的 -/
axiom Rtrans {x y z : Nat} : R x y → R y z → R x z

-- ローカルコンテキストに `R x y` と `R y z` が現れたとき、
-- `Rtrans` をインスタンス化しなさいと grind に指示している
grind_pattern Rtrans => R x y, R y z

example (x y z : Nat) (h₁ : R x y) (h₂ : R y z) : R x z := by
  -- grind で証明できる
  grind

/-
## where による制御

`grind_pattern` コマンドは、`grind` タクティクに定理を再利用させることができるという点では `[grind]` 属性とできることが同じですが、`grind_pattern` コマンドの方がより細かい制御を行えます。

典型的な例として、`grind_pattern` コマンドでは `where` で制約を追加することができ、不要なインスタンスが暴発することを防ぐことができます。

### `=/=` 制約

`=/=` 制約を追加すると、両辺が definitionally equal でないときにのみ定理がインスタンス化されるようになります。
-/

variable {α : Type} [Mul α] [One α]

/-- リストの積 -/
@[grind =]
def List.prod (xs : List α) : α :=
  xs.foldr (· * ·) 1

-- α が可換なモノイドという仮定を足す
variable [@Std.LawfulIdentity α (· * ·) 1]
variable [@Std.Associative α (· * ·)] [@Std.Commutative α (· * ·)]

theorem List.prod_append (xs ys : List α) :
    (xs ++ ys).prod = xs.prod * ys.prod := by
  induction xs with grind

section
  -- 単に「左辺を見つけたらインスタンス化」というルールにすると...
  local grind_pattern List.prod_append => (xs ++ ys).prod

  /-⋆-//--
  trace: [grind.ematch.instance] List.prod.eq_1: ([] ++ []).prod = List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ [])
  [grind.ematch.instance] List.prod_append: ([] ++ []).prod = [].prod * [].prod
  [grind.ematch.instance] List.append_nil: [] ++ [] = []
  [grind.ematch.instance] List.nil_append: [] ++ [] = []
  [grind.ematch.instance] List.foldr_append: List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ []) =
        List.foldr (fun x1 x2 => x1 * x2) (List.foldr (fun x1 x2 => x1 * x2) 1 []) []
  [grind.ematch.instance] List.foldr_nil: List.foldr (fun x1 x2 => x1 * x2) 1 [] = 1
  -/
  #guard_msgs (whitespace := lax) in --#
  example : ([] ++ []).prod = 1 := by
    -- `[] ++ []` に対しても暴発して余計なインスタンス化が実行される
    set_option trace.grind.ematch.instance true in

    grind
end

-- `=/=` 制約を追加して、空リストが混ざっているときはインスタンス化しないように指示
grind_pattern List.prod_append => (xs ++ ys).prod where
  xs =/= []
  ys =/= []

/--
trace: [grind.ematch.instance] List.prod.eq_1: ([] ++ []).prod = List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ [])
[grind.ematch.instance] List.append_nil: [] ++ [] = []
[grind.ematch.instance] List.nil_append: [] ++ [] = []
[grind.ematch.instance] List.foldr_append: List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ []) =
      List.foldr (fun x1 x2 => x1 * x2) (List.foldr (fun x1 x2 => x1 * x2) 1 []) []
[grind.ematch.instance] List.foldr_nil: List.foldr (fun x1 x2 => x1 * x2) 1 [] = 1
-/
#guard_msgs (whitespace := lax) in --#
example : ([] ++ []).prod = 1 := by
  -- `[] ++ []` に対して暴発しなくなる
  set_option trace.grind.ematch.instance true in

  grind
