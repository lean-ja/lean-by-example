/- # decreasing_by

`decreasing_by` は、再帰関数などの停止性（計算が無限に続かないということ）を示し、Lean に定義を受け入れさせるために使われます。

## 使用例

たとえば、以下の関数はそのままでは Lean が停止性を示せないためエラーになってしまいます。
-/
namespace Hidden --#
-- エラーになってしまう
--#--
/--
error: fail to show termination for
  Hidden.Nat.toListNat
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    toListNat (n / 10)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
⊢ n / 10 < n
-/
#guard_msgs in
--#--
def Nat.toListNat (n : Nat) : List Nat :=
  if n == 0 then
    []
  else
    Nat.toListNat (n / 10) ++ [(n % 10)]

end Hidden --#
/- `decreasing_by` に続けて停止することの証明を与えれば Lean に受け入れられるようになります。 -/

def Nat.toListNat (n : Nat) : List Nat :=
  if n == 0 then
    []
  else
    Nat.toListNat (n / 10) ++ [(n % 10)]
decreasing_by
  -- `n ≠ 0 → n / 10 < n` を示す
  grind

-- 動作テスト
#guard Nat.toListNat 1234 = [1, 2, 3, 4]

/- あるいは、`decreasing_by` を使用しなくても、関数内で `have` などを使って停止性を証明しておいても良いです。 -/
namespace Have --#

def Nat.toListNat (n : Nat) : List Nat :=
  if h : n == 0 then
    []
  else
    have : n / 10 < n := by
      grind
    Nat.toListNat (n / 10) ++ [(n % 10)]

end Have --#
/- ## 舞台裏

そもそもなぜ Lean では関数の停止性を示す必要があるのでしょうか？それは、Lean の論理体系の健全性を保つためです。[^recursive]

例として、停止する保証がない関数を定義してみましょう。以下の関数は引数の数列の `f` がいつか `some` になる保証がないので、無限に計算が終わらない可能性があります。
-/
variable {α : Type}

/-- 数列 `f : Nat → Option α` が `some` を返すような最初の `f n` を返す -/
unsafe def search (f : Nat → Option α) (start : Nat) : α :=
  match f start with
  | .some x => x
  | .none => search f (start + 1)

/- ここで問題なのは、この関数 `search` を使うと任意の型の項が構成できてしまうということです。 -/

-- `α` は任意なので、どんな型の項でも作れることになる
unsafe def anything : α := search (fun _ => none) 0

/- したがって特に `Empty` 型の項を作ることもできて、カリー・ハワード同型対応により「型の項を作る」ことは「命題を証明する」ことに対応するので、矛盾が導かれたことになってしまいます。 -/

unsafe example : False := by
  have _ : Empty := anything
  contradiction

/-
[^recursive]: ここで紹介している例は Joachim Breitner さんによる [Recursive definitions in Lean](https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/) というブログ記事から引用しています。
-/
