/- # cases_eliminator

`[cases_eliminator]` 属性は、[`cases`](#{root}/Tactic/Cases.md) タクティクで場合分けをした際の枝を変更します。

より詳しくいうと、[`cases`](#{root}/Tactic/Cases.md) タクティクの `using` キーワードのデフォルトの引数を変更することができます。デフォルトでは、[帰納型](#{root}/Declarative/Inductive.md) `T` に対して `T.casesOn` という定理が自動生成されてそれが暗黙の裡に `using` キーワードの引数として使われますが、`[cases_eliminator]` 属性で別な定理を指定すると、それが使われるようになります。
-/

variable {α : Type}

/-- 遅延評価のリストもどき -/
inductive Many (α : Type) where
  | none
  | more (x : α) (xs : Unit → Many α)

example (xs : Many α) : True := by
  cases xs with
  | none => trivial
  | more x xs =>
    -- xs の型が Unit → Many α になっており、
    -- 必要なとき毎回 xs () で取り出さなければならず面倒
    guard_hyp xs : Unit → Many α
    trivial

/-- Unit が登場しないように工夫した関数 -/
def Many.cons (x : α) (xs : Many α) : Many α :=
  .more x (fun () => xs)

-- Many を定義したときに自動生成される定理
/--
info: Many.casesOn.{u} {α : Type} {motive : Many α → Sort u} (t : Many α) (none : motive Many.none)
  (more : (x : α) → (xs : Unit → Many α) → motive (Many.more x xs)) : motive t
-/
#guard_msgs (whitespace := lax) in #check Many.casesOn

/-- Many.casesOn の more を cons に置き換えたバージョン。
この定理に `[cases_eliminator]` 属性を与えることで、
`casesOn` の代わりにこれがデフォルトで使われるようになる。 -/
@[cases_eliminator]
protected def Many.cons_casesOn.{u} {α : Type} {motive : Many α → Sort u} (t : Many α) (none : motive Many.none)
    (cons : (a : α) → (b : Many α) → motive (Many.cons a b)) : motive t := by
  match t with
  | .none => assumption
  | .more x xs =>
    exact cons x (xs ())

example (xs : Many α) : True := by
  cases xs

  case none => trivial

  -- case で分割したときのデフォルトのコンストラクタが cons に変わる
  case cons x xs =>
    -- xs の型が Many α になっている！
    guard_hyp xs : Many α
    trivial

/- デフォルトの挙動に戻すには、`using` キーワードに `.casesOn` を渡します。-/

example (x : Many α) : True := by
  cases x using Many.casesOn
  case none => trivial
  case more x => trivial

/- なお [`rcases`](#{root}/Tactic/Rcases.md) には影響しません。 -/

example (xs : Many α) : True := by
  rcases xs with _ | _

  case none => trivial

  case more _ xs =>
    -- xs の型が Unit → Many α になっている
    guard_hyp xs : Unit → Many α
    trivial
