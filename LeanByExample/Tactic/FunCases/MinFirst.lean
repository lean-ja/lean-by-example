
variable {α : Type} [LE α] [DecidableEq α] [DecidableLE α]

instance : Min α := minOfLe

/-- リストの最小値を先頭に持ってくる -/
@[simp, grind]
def minFirst (xs : List α) : List α :=
  match h : xs with
  | [] => []
  | x :: xs =>
    let μ := List.min (x :: xs) (h := by simp)
    let rest := List.erase (x :: xs) μ

    -- 関数定義の中で補題を示しておくと、`fun_cases` で再利用できる
    have : (μ :: rest).length = (x :: xs).length := by
      grind [List.min_mem]

    μ :: rest

@[grind =]
theorem minFirst_length (xs : List α) :
    (minFirst xs).length = xs.length := by
  -- 普通にinductionすると失敗する
  fail_if_success induction xs with grind

  -- `fun_cases` を使うと成功する
  fun_cases minFirst xs with grind
