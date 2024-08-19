/- # 騎士と悪党のパズル

騎士(Knight)と悪党(Knave)の論理パズルは、著名な論理学者 Raymond Smullyan によって考案されたとされています。それ以来様々な変種が考案され続けてきました。ここでは、その中でも基本的なものを Lean で形式化し、解いていきます。

## 概要

[Critical thinking web](https://philosophy.hku.hk/think/logic/knights.php) から問題を引用します。まずは自然言語で問題文を述べましょう。

```admonish info title=""
ある島には、騎士と悪党しか住んでいません。すべての島民は騎士であるか悪党であるかのいずれかです。騎士が話すことは常に真であり、悪党が話すことは常に偽です。

あなたはゾーイとメルという２人の島民に出会いました。
ゾーイは「メルは悪党です」と言いました。
メルは「ゾーイも私も悪党ではありません」と言いました。
さて、ゾーイとメルはそれぞれ騎士か悪党のどちらでしょうか？
```

## 形式化

さっそく形式化を行っていきます。まず、ある島があってそこには騎士と悪党しか住んでいないというところですが、これは `Islander` という型に `knight` と `knave` という部分集合が存在するというように形式化できます。そのうえで、島民が騎士か悪党のどちらかであることを `axiom` コマンドで仮定しましょう。

ここでは後で便利なように `simp` 補題も示しておくことにします。
-/

/-- その島の住民を表す型 -/
opaque Islander : Type

/-- Islander の部分集合として定義した騎士の全体 -/
opaque knight : Islander → Prop

/-- Islander の部分集合として定義した悪党の全体 -/
opaque knave : Islander → Prop

/-- 人は騎士か悪党のどちらか -/
axiom knight_or_knave (p : Islander) : knight p ∨ knave p

/-- 人が騎士かつ悪党であることはない -/
axiom knight_ne_knave (p : Islander) : ¬(knight p ∧ knave p)

/-- 騎士でないことと悪党であることは同値 -/
@[simp] theorem of_not_knight {p : Islander} : ¬ knight p ↔ knave p := by
  have or := knight_or_knave p
  have ne := knight_ne_knave p
  constructor
  all_goals
    intro h
    simp_all

/-- 悪党でないことと騎士であることは同値 -/
@[simp] theorem of_not_knave {p : Islander} : ¬ knave p ↔ knight p := by
  have or := knight_or_knave p
  have ne := knight_ne_knave p
  constructor
  all_goals
    intro h
    simp_all

/-
```admonish warning title="注意"
`Islander` 型を `knight` と `knave` の２つのコンストラクタを持つ帰納型として定義すると、島民が２人しかいないことになってしまって、正しい表現にならないことに注意して下さい。
```
-/

/- これでゾーイとメルが島民であり、騎士か悪党かのどちらかであるということは次のように表現できます。-/

/-- ゾーイ -/
axiom zoey : Islander

/-- メル -/
axiom mel : Islander

/- 正直者であるとか嘘つきであるということを表現するために、誰がなんと発言したかを表現するための関数を用意します。その上で、それぞれの発言を愚直に形式化していきます。 -/

/-- p さんが body という命題を話したという事実を表す命題 -/
opaque Islander.say (p : Islander) (body : Prop) : Prop

variable {p : Islander} {body : Prop}

/-- 騎士の発言内容はすべて真実 -/
axiom statement_of_knight (h : knight p) (say : p.say body) : body

/-- 悪党の発言内容はすべて偽 -/
axiom statement_of_knave (h : knave p) (say : p.say body) : ¬body

/-- ゾーイは「メルは悪党だ」と言った -/
axiom zoey_says : zoey.say (knave mel)

/-- メルは「ゾーイもメルも悪党ではない」と言った -/
axiom mel_says : mel.say (¬ knave zoey ∧ ¬ knave mel)

/- ここまでで問題文の前提部分の形式化は完了です。

残っているのは、「ゾーイとメルはそれぞれ騎士か悪党のどちらですか」と問う部分です。これは少し難しいです。

考えてみると、Lean で（証明すべき命題がわかっているときに）何かを証明するのはよくありますが、与えられた前提から何が言えるのかを明確なゴールなしに組み立てていくのはあまり見ないということにお気づきになるでしょう。この問題も、もし問いの内容が「ゾーイが騎士であることを示せ」とか「ゾーイが悪党であることを示せ」だったならば、今までの準備の下で簡単に形式化ができますが、「騎士なのか悪党なのか決定せよ」なので少し複雑になります。

ここでの解決方法は、`Solution` という型クラスを `inductive class` コマンドで作成し、そのインスタンスを作ってくださいという形式にすることです。
-/

/-- `p` が騎士か悪党のどちらなのか知っていることを表す型クラス -/
class inductive Solution (p : Islander) : Type where
  | isKnight : knight p → Solution p
  | isKnave : knave p → Solution p

/- `class inductive` というものをあまり見たことがないかもしれませんが、これは普通の型クラスと異なりコンストラクタが複数ある型クラスを定義することができます。この `Solution` の場合、`p : Islander` に対してインスタンスを作成するときに、インスタンスが `isKnight` から来るのか `isKnave` から来るのか明示しなければなりません。そしてそのために、それぞれ `p` が騎士であるか悪党であるかのどちらかの証明が引数に要求されることになります。

## 問題

以上の準備の下で、問題は次のように表現できます。以下の `sorry` の部分を埋めてください。
-/
--##--
theorem zoey_is_not_knave : ¬ knave zoey := by
  -- ゾーイが悪党だと仮定する
  intro h

  have mel_is_knight : knight mel := by
    -- ゾーイの発言は偽なので、メルは悪党ではない
    have := statement_of_knave h zoey_says

    -- よってメルは騎士
    simpa [of_not_knave] using this

  -- メルが騎士なので、メルの発言は真
  have mel_says_truth := statement_of_knight mel_is_knight mel_says

  -- したがってゾーイは騎士
  have : knight zoey := by
    simp only [of_not_knave] at mel_says_truth
    simp_all

  -- これは仮定に矛盾
  simp_all [knight_ne_knave]

/-- ゾーイは騎士である -/
theorem zoey_is_knight : knight zoey := by
  have := zoey_is_not_knave
  simpa using this

/-- メルは悪党 -/
theorem mel_is_knave : knave mel := by
  -- ゾーイは騎士なのでゾーイの発言は真であり、
  -- よってメルは悪党
  exact statement_of_knight zoey_is_knight zoey_says
--##--

-- ゾーイは騎士か悪党か？
noncomputable instance : Solution zoey := by
  -- sorry
  apply Solution.isKnight
  exact zoey_is_knight
  -- sorry

-- メルは騎士か悪党か？
noncomputable instance : Solution mel := by
  -- sorry
  apply Solution.isKnave
  exact mel_is_knave
  -- sorry