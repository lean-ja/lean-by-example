/- # 天使と悪魔の論理パズル

次の古典的な論理パズルを Lean で解いてみましょう。

> 目の前に2本の道がある。片方は天国へ、片方は地獄へ続く。
> そこに2人の番人がいて、一方は天使で、もう一方は悪魔である。
> 天使は常に真実を言い、悪魔は必ず嘘をつく。
> どちらが天使で、どちらが悪魔なのかは分からない。
> どちらか一人に一つだけ YES / NO で答えられる質問をすることが許されている。
> なお番人はすべてを知っており、質問に「わからない」と返答することはないものとする。
> 天国へ続く道を特定するには、どのような質問をすればよいだろうか？

-/

/-
## 問題文の状況を Lean で表現する

Lean でプログラムを書くとき往々にしてそうであるように、まずは適切なデータ型を定義するところから始めましょう。２人の番人がいて、２つの道があるという状況は次のように書けます。
-/

/-- 番人 -/
inductive Guardian where
  /-- 左の番人 -/
  | left
  /-- 右の番人 -/
  | right
deriving BEq

/-- 道 -/
inductive Road where
  /-- 左の道 -/
  | left
  /-- 右の道 -/
  | right
deriving BEq

/-
問題のゴールを表現するのには、これに比べると少し自由度があります。「どのような質問をすればよいか？」という問いなので、意味のある質問文をすべて含むような型 `Question` を定義して、その中にある適切な質問文 `q : Question` を探索して見つけるという風に解釈しましょう。

そこで、「この問題の問題設定において、意味のある質問とはどのようなものか」を考える必要があります。まず確定で言えることとして、以下のような質問は可能であるべきでしょう。

* あなたは天使なのか、それとも悪魔なのかと訊く
* 左の道は天国へ続く道なのか、それとも右の道は天国へ続く道なのかと訊く

また、`p, q : Question` が意味のある質問であるならば、「`p` または `q` ですか？」といった質問も意味を持つはずですね。そう考えると、質問全体の型 `Question` を、次のように定義できそうです。
-/

inductive Question where
  /-- `g` は天使ですか？という質問 -/
  | angel (g : Guardian)
  /-- `r` は天国へ続きますか？という質問 -/
  | toHeaven (r : Road)
  /-- `q` を否定した質問。
  「左の人は悪魔ですか？」とか、「左の道は地獄へ続きますか？」という質問ができる -/
  | not (q : Question)
  /-- `q` または `p` ですかという質問 -/
  | or (q p : Question)
  /-- `q` かつ `p` ですかという質問 -/
  | and (q p : Question)
  /-- `q` と `p` は同値ですかという質問 -/
  | iff (q p : Question)

/- このようにして探索する対象の質問全体 `Question` が定義できたので、次は求める質問が満たすべき条件を定式化します。

問題文では「天国へ続く道を特定するにはどうすればいいか」という表現になっていますが、２人の番人のどちらが正直者（天使）でどちらが悪魔（嘘つき）なのかわからないのですから、「相手が天使であろうと悪魔であるかに関係なく、道の行く先だけを反映して答えが返ってくるような質問」であるというのが満たすべき条件だといえます。それをきちんと定式化すればよさそうです。
-/

/-- 状態 -/
structure State where
  /-- 左の人と右の人、どちらが天使なのか。残り片方が悪魔 -/
  angel : Guardian
  /-- 左の道と右の道、どちらが天国へ続く道なのか。残り片方が地獄行き。 -/
  toHeaven : Road

/-- `s` という状況下における `q : Question` という質問に対する真偽。
回答ではないので、嘘は入らない -/
def truth (s : State) (q : Question) : Bool :=
  match q with
  | .angel tgt => s.angel == tgt
  | .toHeaven tgt => s.toHeaven == tgt
  | .not q => !truth s q
  | .or q p => truth s q || truth s p
  | .and q p => truth s q && truth s p
  | .iff q p => truth s q == truth s p

/-- `s` という状況下で、`g : Guardian` に対して `q : Question` という質問をした時の答え。
YES か NO で返答が返ってくるが、`true` が YES に対応する。 -/
def answer (s : State) (respond : Guardian) (q : Question) : Bool :=
  if s.angel == respond then
    truth s q
  else
    !truth s q

/- 定義がきちんとできたかどうか確かめるために少しテストをしてみます。 -/

/-- 左の人が天使で左の右が天国行き -/
def exampleState : State := { angel := .left, toHeaven := .left }

-- 右の人（悪魔）に向かって、あなたは天使ですか？と訊いた時の返事は YES
#guard answer exampleState .right (.angel .right)

-- 左の人（天使）に向かって、あなたは天使ですか？と訊いたときの返事は YES
#guard answer exampleState .left (.angel .left)

-- 右の人（悪魔）に向かって、あなたは悪魔ですか？と訊いた時の返事は NO
#guard answer exampleState .right (.not (.angel .right)) == false

/-
最後に、求めるべき質問の条件を定式化します。それは、相手が悪魔だろうと天使だろうと、どんな状況でも道の行く先だけに依存して返事が変わるような質問であることです。
-/

/-- 番人をすべて並べたリスト -/
def allGuardians : List Guardian := [.left, .right]

/-- 道をすべて並べたリスト -/
def allRoads : List Road := [.left, .right]

/-- 状態をすべて並べたリスト -/
def allStates : List State := [
  { angel := .left, toHeaven := .left },
  { angel := .left, toHeaven := .right },
  { angel := .right, toHeaven := .left },
  { angel := .right, toHeaven := .right }
]

/-- 良い質問かどうかを判定する。
どんな状態であっても、道の行く先だけを判定できる質問かどうか -/
def Question.goodFor (q : Question) (respond : Guardian) : Bool :=
  allStates.all fun s =>
    answer s respond q == (s.toHeaven == .left)

#guard (Question.angel .left).goodFor .left == false
#guard (Question.angel .left).goodFor .left == false
