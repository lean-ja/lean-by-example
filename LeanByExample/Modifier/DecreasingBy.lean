/- # decreasing_by

`decreasing_by` は、再帰関数などの停止性（計算が無限に続くことがなく、値が一意に決まること）を示し、Lean に定義を受け入れさせるために使われます。

## 使用例

たとえば、以下の関数はそのままでは Lean が停止性を示せないためエラーになってしまいます。
-/
namespace Hidden --#
-- エラーになってしまう
/--
error: fail to show termination
-/
#guard_msgs (substring := true) in --#
def Nat.toListNat (n : Nat) : List Nat :=
  if n == 0 then
    []
  else
    Nat.toListNat (n / 10) ++ [(n % 10)]

end Hidden --#
/- `decreasing_by` に続けて停止することの証明を与えれば Lean に受け入れられるようになります。再帰のたびに(無限には減少できない)引数が真に減少することを示せば十分です。 -/

def Nat.toListNat (n : Nat) : List Nat :=
  if n == 0 then
    []
  else
    Nat.toListNat (n / 10) ++ [(n % 10)]
decreasing_by
  -- `n ≠ 0 → n / 10 < n` を示す
  guard_target =ₛ n / 10 < n

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
/- ## 部分関数を禁止するのはなぜか？ { #PartialNotAllowed }

そもそもなぜ Lean では関数の停止性を示す必要があるのでしょうか？それは、Lean の論理体系の健全性を保つためです。[^recursive]

[カリー・ハワード同型対応](#{root}/Type/Prop.md#CH)によれば「帰納法は再帰」なので、停止しない再帰を許すことは直接的に「終了しない帰納法」を許すことに繋がり、矛盾をもたらすことになってしまいます。
-/

-- unsafe を使うと終わらない帰納法が使えるので、何でも証明できる
unsafe def loop_thm (P : Prop) : P :=
  loop_thm P

unsafe example : False := loop_thm False

/-
定理ではなくて通常の関数の場合も、停止しない関数を野放図に許すと矛盾を導くことができます。例として、以下の「`Option` 値の点列から `some` であるようなものを探す関数」を考えてみましょう。この関数は引数の点列の `f` がいつか `some` になる保証がないので、無限に計算が終わらない可能性があります。
-/
variable {α : Type}

/-- 点列 `f : Nat → Option α` が `some` を返すような最初の `f n` を返す -/
unsafe def search (f : Nat → Option α) (start : Nat) : α :=
  match f start with
  | .some x => x
  | .none => search f (start + 1)

/- ここで問題なのは、この関数 `search` を使うと任意の型の項が構成できてしまうということです。-/

-- `α` は任意なので、どんな型の項でも作れることになる
unsafe def anything : α := search (fun _ => none) 0

/- したがって特に `Empty` 型の項を作ることもできて、[カリー・ハワード同型対応](#{root}/Type/Prop.md#CH)により「型の項を作る」ことは「命題を証明する」ことに対応するので、矛盾が導かれたことになってしまいます。 -/

unsafe example : False := by
  have _ : Empty := anything
  contradiction

/-
[^recursive]: ここで紹介している例は Joachim Breitner さんによる [Recursive definitions in Lean](https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/) というブログ記事から引用しています。
-/
