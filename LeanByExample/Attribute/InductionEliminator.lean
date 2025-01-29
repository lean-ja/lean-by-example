/- # induction_eliminator

`[induction_eliminator]` 属性は、帰納法の枝を変更することを可能にします。

より詳しくいうと、[`induction`](#{root}/Tactic/Induction.md) タクティクの `using` キーワードのデフォルトの引数を変更することができます。デフォルトでは、[帰納型](#{root}/Declarative/Inductive.md) `T` に対して `T.rec` (および `T.recOn` )という定理が自動生成されてそれが暗黙の裡に `using` キーワードの引数として使われますが、`[induction_eliminator]` 属性で別な定理を指定すると、それが使われるようになります。
-/

variable {α : Type}

/-- 遅延評価のリストもどき -/
inductive Many (α : Type) where
  | none
  | more (x : α) (xs : Unit → Many α)

/-- Many に対する合併関数 -/
def Many.union : Many α → Many α → Many α
  | .none, ys => ys
  | .more x xs, ys => Many.more x (fun () => union (xs ()) ys)

-- Many に関する定理を帰納法で示す例
example (xs : Many α) : Many.union xs Many.none = xs := by
  induction xs with
  | none => rfl
  | more x xs ih =>
    -- ここで xs の型は Unit → Many α になっている
    -- 必要なとき毎回 xs () で取り出さなければならず面倒
    guard_hyp xs : Unit → Many α

    simp [Many.union, ih]

/-- Unit が登場しないように工夫した関数 -/
def Many.cons (x : α) (xs : Many α) : Many α :=
  .more x (fun () => xs)

-- Many を定義したときに自動生成される定理
/--
info: Many.rec.{u} {α : Type} {motive : Many α → Sort u} (none : motive Many.none)
  (more : (x : α) → (xs : Unit → Many α) → ((a : Unit) → motive (xs a)) → motive (Many.more x xs)) (t : Many α) :
  motive t
-/
#guard_msgs (whitespace := lax) in #check Many.rec

-- Many.rec の `Many.more` の部分を `Many.cons` に置き換えた定理を作る。
-- これに `[induction_eliminator]` 属性を与えることで、
-- コンストラクタ `Many.more` の代わりに `Many.cons` が使えるようになる
@[induction_eliminator]
protected def Many.cons_rec.{u} {α : Type} {motive : Many α → Sort u}
  (none : motive Many.none)
  (cons : (a : α) → (b : Many α) → (motive b) → motive (Many.cons a b))
    : (t : Many α) → motive t
  | .none => none
  | .more x xs => cons x (xs ()) (Many.cons_rec none cons (xs ()))

example (xs : Many α) : Many.union xs Many.none = xs := by
  induction xs with
  | none => rfl
  | cons x xs ih =>
    -- ここで xs の型が Many α になっている！
    -- 毎回 `xs ()` などと書く必要がなくなった
    guard_hyp xs : Many α

    simp [Many.union, Many.cons, ih]

/- `[induction_eliminator]` を設定する前の挙動に戻すには、`using` キーワードに明示的に `.rec` 定理を与えます。 -/

example (xs : Many α) : True := by
  -- 明示的に指定すれば， 元の挙動に戻せる
  induction xs using Many.rec with
  | none => trivial
  | more _ xs _ =>
    -- 元のように Many.more が使われる
    guard_hyp xs : Unit → Many α

    trivial
