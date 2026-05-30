variable {α : Type} [Mul α] [One α]

/-- リストの積 -/
@[grind =]
def List.myprod (xs : List α) : α :=
  xs.foldr (· * ·) 1

-- 注意: 既に定義されているものが存在する
#check List.prod

-- α がモノイドという仮定を足す
variable [@Std.LawfulIdentity α (· * ·) 1]
variable [@Std.Associative α (· * ·)]

@[simp, grind =]
theorem List.myprod_cons (x : α) (xs : List α) :
    (x :: xs).myprod = x * xs.myprod := by
  grind

theorem List.myprod_append (xs ys : List α) :
    (xs ++ ys).myprod = xs.myprod * ys.myprod := by
  induction xs with
  | nil => grind
  | cons x xs ih =>
    simp_all [Std.Associative.assoc]

section
  -- 単に「左辺を見つけたらインスタンス化」というルールにすると...
  local grind_pattern List.myprod_append => (xs ++ ys).myprod

  /--
  trace: [grind.ematch.instance] List.myprod.eq_1: ([] ++ []).myprod = List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ [])
  [grind.ematch.instance] List.myprod_append: ([] ++ []).myprod = [].myprod * [].myprod
  [grind.ematch.instance] List.append_nil: [] ++ [] = []
  [grind.ematch.instance] List.nil_append: [] ++ [] = []
  [grind.ematch.instance] List.foldr_append: List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ []) =
        List.foldr (fun x1 x2 => x1 * x2) (List.foldr (fun x1 x2 => x1 * x2) 1 []) []
  [grind.ematch.instance] List.foldr_nil: List.foldr (fun x1 x2 => x1 * x2) 1 [] = 1
  -/
  #guard_msgs (whitespace := lax) in --#
  example : ([] ++ []).myprod = 1 := by
    -- `[] ++ []` に対しても暴発して余計なインスタンス化が実行される
    set_option trace.grind.ematch.instance true in

    grind
end

-- `=/=` 制約を追加して、空リストが混ざっているときはインスタンス化しないように指示
grind_pattern List.myprod_append => (xs ++ ys).myprod where
  xs =/= []
  ys =/= []

/--
trace: [grind.ematch.instance] List.myprod.eq_1: ([] ++ []).myprod = List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ [])
[grind.ematch.instance] List.append_nil: [] ++ [] = []
[grind.ematch.instance] List.nil_append: [] ++ [] = []
[grind.ematch.instance] List.foldr_append: List.foldr (fun x1 x2 => x1 * x2) 1 ([] ++ []) =
      List.foldr (fun x1 x2 => x1 * x2) (List.foldr (fun x1 x2 => x1 * x2) 1 []) []
[grind.ematch.instance] List.foldr_nil: List.foldr (fun x1 x2 => x1 * x2) 1 [] = 1
-/
#guard_msgs (whitespace := lax) in --#
example : ([] ++ []).myprod = 1 := by
  -- `[] ++ []` に対して暴発しなくなる
  set_option trace.grind.ematch.instance true in

  grind
