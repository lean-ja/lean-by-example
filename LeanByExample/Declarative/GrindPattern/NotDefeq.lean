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
