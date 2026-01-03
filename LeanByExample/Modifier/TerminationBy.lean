/- # termination_by

`termination_by` 句(termination_by clause)は、再帰関数が有限回の再帰で停止することを Lean にわかってもらうために、「再帰のたびに減少する指標」を指定します。
-/
-- 何も指定しないと、停止することが Lean にはわからないのでエラーになる
/-⋆-//--
error: fail to show termination for
  M
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    M (n + 11)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n #1
1) 33:7-17 ?  ≤
2) 33:4-18 _  ?

#1: 100 - n

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in --#
/-- McCarthy の 91 関数 -/
def M (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    M (M (n + 11))

/- 以下のように、`termination_by` で「再帰適用で減少していくもの」を指定することができ、うまくいけばエラーがなくなります。[^timo]-/

/-- McCarthy の 91 関数 -/
def Mc91 (n : Nat) : Nat :=
  (M n).val
where
  M (n : Nat) : { m : Nat // m ≥ n - 10 } :=
    if h : n > 100 then
      ⟨n - 10, by omega⟩
    else
      have : n + 11 - 10 ≤ M (n + 11) := (M (n + 11)).property
      have lem : n - 10 ≤ M (M (n + 11)) := calc
        _ ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property

      ⟨M (M (n + 11)), lem⟩
  -- 再帰のたびに n が 101 に近づいていくことを Lean に教えてあげる
  termination_by 101 - n

/- ## 構造的再帰と整礎再帰

### 構造的再帰

再帰関数を定義しようとすると、Lean はその関数が「どんな入力に対しても有限回の再帰で停止すること」を証明しようとします。関数によって、その自動証明が簡単なことと難しいことがあります。

簡単な場合の代表例は、引数が帰納型 `T` の項になっていて、再帰呼び出しによって `T` の「より小さい」項を引数として渡す場合です。ここで、「より小さい」というのは帰納型の基底ケースからのコンストラクタの適用回数によって測ります。このような再帰は **構造的再帰(structural recursion)** と呼ばれます。

構造的再帰の場合は停止性の証明は簡単なので、基本的に Lean が自動で証明してくれます。
-/

/-- 構造的再帰の例。階乗関数。-/
def Nat.factorial (n : Nat) : Nat :=
  -- Nat の帰納的定義の構造に基づいて再帰しているので、
  -- 引数が「より小さくなる」ことは明らかで、 Lean は自動で停止性を証明できる
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * Nat.factorial m

example : Nat.factorial 5 = 120 := by rfl

/-
構造的再帰の場合は何も指定しなくても Lean が自動的に停止性を証明してくれることが大半ですが、構造的再帰であると明示することもできて、その場合は `termination_by structural` と書きます。
-/

/-- 構造的再帰の例。 -/
def swapAlt {α : Type} (xs : List α) : List α :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: zs => y :: x :: swapAlt zs
termination_by structural xs

example : swapAlt [1, 2, 3, 4] = [2, 1, 4, 3] := by
  rfl

/-
### 整礎再帰

構造的再帰では停止性は証明できなくても、別の方法で停止性が自動的に保証できる場合があります。

例えば、配列のインデックスを左から見ていく操作のように、「再帰呼び出しのたびに引数が増加していてもある上限を超えないことが分かっている場合」は停止性が保証できます。
-/

/-- `Array.search`のための補助関数。
再帰呼び出しのたびに `i` が増加するが、増加に上限があるので必ず停止する -/
def Array.searchAux {α : Type} (as : Array α) (i : Nat) (P : α → Bool) : Bool :=
  if h : i < as.size then
    if P (as[i]) then
      true
    else
      Array.searchAux as (i + 1) P
  else
    true
-- 再帰のたびに i は増加するが、
-- 配列のサイズを超えることはないので停止することを Lean に教えてあげる
termination_by as.size - i

/-- 配列の要素であって、述語 `P` を満たすものを探す -/
def Array.search {α : Type} (as : Array α) (P : α → Bool) : Bool :=
  Array.searchAux as 0 P

#guard #[1, 2, 3].search (· % 2 = 0)

/-
一般に（無限に小さくなり続けることはない）ある指標が、再帰呼び出しのたびに減少していく場合、停止性を保証するのに利用することができます。このような再帰は **整礎再帰(well-founded recursion)** と呼ばれます。`termination_by` 句は、整礎再帰のためにどの指標を利用するかを Lean に伝えるための構文であると言うことができます。

Lean は賢いので、多くのシンプルなケースについては `termination_by` 句を省略することができますが、その場合でも整礎再帰であることに変わりはありません。
-/

/-- 整除関数。
構造的再帰ではないが、Lean が自動的に停止性を証明できる -/
def div (x y : Nat) : Nat :=
  if h : y = 0 then
    0
  else if x < y then
    0
  else
    1 + div (x - y) y

#guard div 10 3 = 3

/-
[^timo]: このコード例は、Lean 公式 Zulip の [how to show termination of McCarthy `M`](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/how.20to.20show.20termination.20of.20McCarthy.20.60M.60/with/442289266) というトピックにおける Timo Carlin-Burns さんの投稿を参考にしています。
-/
