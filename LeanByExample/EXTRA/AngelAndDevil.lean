/- # 天使と悪魔の論理パズル

次の古典的な論理パズルを Lean で解いてみましょう。

> 目の前に2本の道がある。
> 片方は天国へ、片方は地獄へ続く。
>
> そこに2人の番人がいて、一方は天使で、もう一方は悪魔である。
> 天使は常に真実を言い、悪魔は必ず嘘をつく。
> どちらが天使で、どちらが悪魔なのかは分からない。
>
> どちらか一人に一つだけ YES / NO で答えられる質問をすることが許されている。
> なお番人はすべてを知っており、質問に「わからない」と返答することはないものとする。
>
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
deriving BEq, Repr

/-- 道 -/
inductive Road where
  /-- 左の道 -/
  | left
  /-- 右の道 -/
  | right
deriving BEq, Repr

/-
問題のゴールを表現するのには、これに比べると少し自由度があります。「どのような質問をすればよいか？」という問いなので、意味のある質問文をすべて含むような型 `Question` を定義して、その中にある適切な質問文 `q : Question` を探索して見つけるという風に解釈しましょう。

そこで、「この問題の問題設定において、意味のある質問とはどのようなものか」を考える必要があります。まず確定で言えることとして、以下のような質問は可能であるべきでしょう。

* 左の人は悪魔ですか？と訊く
* あなたは天使なのかと訊く
* 左の道は天国へ続く道なのかと訊く

ここで注意が必要なのは、「あなた」という言葉は、質問に答える相手によって指す番人が変わるという点です。そこで、番人を指す表現として「左の番人」「右の番人」のほかに、「あなた」「あなたではない方」を扱えるようにします。

また、`p, q : Question` が意味のある質問であるならば、「`p` または `q` ですか？」といった質問も意味を持つはずですね。そう考えると、質問全体の型 `Question` を、次のように定義できそうです。
-/

/-- 質問文の中で番人を指す表現 -/
inductive GuardianRef where
  /-- 左の番人 -/
  | left
  /-- 右の番人 -/
  | right
  /-- 質問に答える番人自身 -/
  | you
  /-- 質問に答える番人ではない方 -/
  | other
deriving BEq, Repr

/-- 反対側の番人 -/
def Guardian.other (g : Guardian) : Guardian :=
  match g with
  | .left => .right
  | .right => .left

inductive Question where
  /-- `gr` は天使ですか？という質問 -/
  | angel (gr : GuardianRef)
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
deriving BEq, Repr

/- このようにして探索する対象の質問全体 `Question` が定義できたので、次は求める質問が満たすべき条件を定式化します。

問題文では「天国へ続く道を特定するにはどうすればいいか」という表現になっていますが、２人の番人のどちらが天使でどちらが悪魔なのかわからないのですから、「相手が天使であろうと悪魔であるかに関係なく、道の行く先だけを反映して答えが返ってくるような質問」であるというのが満たすべき条件だといえます。それをきちんと定式化すればよさそうです。
-/

/-- 状態 -/
structure State where
  /-- 左の人と右の人、どちらが天使なのか。残り片方が悪魔 -/
  angel : Guardian
  /-- 左の道と右の道、どちらが天国へ続く道なのか。残り片方が地獄行き。 -/
  toHeaven : Road

/-- 質問に答える番人が決まったときに、番人を指す表現を具体的な番人に解釈する -/
def GuardianRef.eval (respond : Guardian) (gr : GuardianRef) : Guardian :=
  match gr with
  | .left => .left
  | .right => .right
  | .you => respond
  | .other => respond.other

/-- `s` という状況下で、`respond` に向けた `q : Question` という質問に対する真偽。
回答ではないので、嘘は入らない -/
def truth (s : State) (respond : Guardian) (q : Question) : Bool :=
  match q with
  | .angel gr => s.angel == gr.eval respond
  | .toHeaven r => s.toHeaven == r
  | .not q => !truth s respond q
  | .or q p => truth s respond q || truth s respond p
  | .and q p => truth s respond q && truth s respond p
  | .iff q p => truth s respond q == truth s respond p

/-- `s` という状況下で、`g : Guardian` に対して `q : Question` という質問をした時の答え。
YES か NO で返答が返ってくるが、`true` が YES に対応する。 -/
def answer (s : State) (respond : Guardian) (q : Question) : Bool :=
  if s.angel == respond then
    truth s respond q
  else
    !truth s respond q

/- 定義がきちんとできたかどうか確かめるために少しテストをしてみます。 -/

/-- 左の人が天使で左の道が天国行き -/
def exampleState : State := { angel := .left, toHeaven := .left }

-- 右の人（悪魔）に向かって、あなたは天使ですか？と訊いた時の返事は YES
#guard answer exampleState .right (.angel .you)

-- 左の人（天使）に向かって、あなたは天使ですか？と訊いたときの返事は YES
#guard answer exampleState .left (.angel .you)

-- 右の人（悪魔）に向かって、あなたは悪魔ですか？と訊いた時の返事は NO
#guard answer exampleState .right (.not (.angel .you)) == false

/-
最後に、求めるべき質問の条件を定式化します。それは、相手が悪魔だろうと天使だろうと、どんな状況でも道の行く先だけに依存して返事が変わるような質問であることです。
-/

/-- 番人をすべて並べたリスト -/
def allGuardians : List Guardian := [.left, .right]

/-- 状態をすべて並べたリスト -/
def allStates : List State := [
  { angel := .left, toHeaven := .left },
  { angel := .left, toHeaven := .right },
  { angel := .right, toHeaven := .left },
  { angel := .right, toHeaven := .right }
]

-- `List` をモナドのインスタンスにする
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

/-- 良い質問かどうかを判定する -/
def Question.good (q : Question) : Bool :=
  let results : List Bool := do
    let respond ← allGuardians
    let s ← allStates
    return answer s respond q == (s.toHeaven == .left)
  results.foldl (· && ·) true

/- ## 探索

これで「求めるべき質問」を定義することができました。あとはそのような質問を探索して見つけるだけです。

探索する対象は、質問全体の空間 `Question` なわけですが、この型には無限に多くの項があるので、全部探索するわけにはいきません。複雑さを測る尺度を用意して、ある程度簡単なものに限って探索することにしましょう。例えば、質問 `q : Question` の構造の深さを次のように定義すれば、深さが一定以下の質問は有限個になるので全探索できるようになります。
-/

/-- 質問の深さ -/
def Question.depth (q : Question) : Nat :=
  match q with
  | .angel _ => 0
  | .toHeaven _ => 0
  | .not q => q.depth + 1
  | .or q p => max q.depth p.depth + 1
  | .and q p => max q.depth p.depth + 1
  | .iff q p => max q.depth p.depth + 1

/- まず深さが小さいものから調べましょう。深さゼロの原子的な質問は有限個です。番人を指す表現が4個、道が2本なので、ここから作れる原子的質問は全部で6個しかありません。 -/

/-- 原子的な質問をすべて並べたリスト -/
def atomicQuestions : List Question := [
  .angel .left,
  .angel .right,
  .angel .you,
  .angel .other,
  .toHeaven .left,
  .toHeaven .right
]

-- この中に良い質問はない
#guard atomicQuestions.filter Question.good == []

/-
深さゼロの質問の中に良い質問はありませんでした。次は深さ１の質問を調べてみましょう。深さ１の質問は、原始的な質問に二項演算を適用したものからなっていて、全部で `6 + 6 * 6 * 3 = 114` 個しかありません。これも全探索できます。

探索は、`List` のモナドインスタンスを使うと簡単に書くことができます。
-/

/-- 深さ１の質問文全体 -/
def depth1Questions : List Question :=
  let ofNot : List Question := atomicQuestions.map Question.not
  let ofBinary : List Question := do
    let q1 ← atomicQuestions
    let q2 ← atomicQuestions
    let op ← [Question.or, Question.and, Question.iff]
    return op q1 q2
  ofBinary ++ ofNot

-- 114 個しかない
#guard depth1Questions.length == 114

/- すると早くもこの中から解が見つかります。複数の解が出ますが、対称性によって複数出ているだけであり、本質的には「あなたは天使である」と「左の道は天国へ続く」は同値ですか？という質問のバリエーションであるようです。 -/

/--
info:
[Question.iff (Question.angel (GuardianRef.you)) (Question.toHeaven (Road.left)),
 Question.iff (Question.angel (GuardianRef.other)) (Question.toHeaven (Road.right)),
 Question.iff (Question.toHeaven (Road.left)) (Question.angel (GuardianRef.you)),
 Question.iff (Question.toHeaven (Road.right)) (Question.angel (GuardianRef.other))]
-/
#guard_msgs (whitespace := lax) in --#
#eval depth1Questions.filter Question.good

/-
質問している相手が天使だろうと悪魔だろうと、左の道が天国行きであれば YES、左の道が地獄行きであれば NO という返事が返ってきます。これでこのパズルは解けました。
-/
