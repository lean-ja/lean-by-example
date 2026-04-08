variable {α : Type} [LE α] [DecidableEq α] [DecidableLE α]

instance : Min α := minOfLe

/-- リストの最小値を先頭に持ってくる -/
@[simp, grind]
def minFirst (xs : List α) : List α :=
  match h : xs with
  | [] => []
  | x :: xs =>
    -- `x :: xs` の最小値を `μ` とする
    let μ := List.min (x :: xs) (h := by simp)

    -- `x :: xs` から `μ` を削除したリストを `rest` とする
    let rest := List.erase (x :: xs) μ

    -- `μ` は（最小値なので当然）`x :: xs` に含まれる
    have : μ ∈ x :: xs := by
      exact List.minOn?_mem rfl

    -- 関数定義の中で補題を示しておくと、`fun_cases` で再利用できる
    have : (μ :: rest).length = (x :: xs).length := by
      grind

    μ :: rest

@[grind =]
theorem minFirst_length (xs : List α) :
    (minFirst xs).length = xs.length := by
  -- 普通にinductionすると失敗する
  fail_if_success
    induction xs with grind only [minFirst]

  -- `fun_cases` を使うと成功する
  fun_cases minFirst xs with grind only [minFirst]
