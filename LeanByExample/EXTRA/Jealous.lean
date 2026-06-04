/- # 嫉妬深い夫たちの川渡りパズル

**嫉妬深い夫の問題(Jealous Husbands Problem)** と呼ばれる、以下の古典的なパズルを Lean で解いてみましょう。

> 3 組の夫婦が川を渡らなければならないが、以下のような制約がある。
>
> * 船が一隻あるが、一度に２人までしか乗ることができない。
> * 船は、当然だが誰か漕ぐ人がいなければ動かすことができない。
> * 全ての人が船を漕ぐことができる。
> * どの男性も大変嫉妬深いので、川のこちら岸にいるときも、向こう岸にいるときも、船に乗っているときも、自分がいないときに自分の妻と他の男性が一緒にいることを許さない。
>
> この制約条件のもとで全員が川を渡って向こう岸に辿り着くことはできるだろうか？

-/
import Std --#
/- ## 問題文を Lean で表現する

まずは問題文の状況を Lean で表現してみます。男性と女性が３人ずつ、合計で６人いるのですから次のような型を考えると良さそうです。
-/

/-- 人間 -/
inductive Person where
  /-- 男性 -/
  | man (id : Fin 3)
  /-- 女性 -/
  | woman (id : Fin 3)
deriving Inhabited, BEq

/- 形式化がうまくいっているのか見るために、今いる登場人物全体、男性全体、女性全体といったものを表現できることを確かめておきましょう。 -/

/-- 男性全体 -/
def men := [0, 1, 2].map Person.man

/-- 女性全体 -/
def women := [0, 1, 2].map Person.woman

/-- 登場人物全体 -/
def people := men ++ women

/- 夫婦であるような男女ペアと、そうでない男女ペアが存在するというのも表現しなければいけません。配偶者を取得する関数を用意します。実装がシンプルになるので、同一 `id` を持つ男性と女性が夫婦であることにします。
-/

/-- 配偶者を取得する -/
def Person.spouse (p : Person) : Person :=
  match p with
  | .man id => .woman id
  | .woman id => .man id

/-
次に、人々の状態を表す型が欲しいです。川の両岸にいま誰がいて、船はどちらに停泊していて、船に誰が乗っていて、船がこちら岸と向こう岸のどちらにいるのか、といった状態をこの型で表現したいです。
-/

/-- 岸 -/
inductive Bank where
  /-- こちら岸 -/
  | here
  /-- 向こう岸 -/
  | there
deriving Inhabited, BEq

/-- 人のいる場所 -/
inductive Place where
  /-- 岸にいる -/
  | ofBank (bank : Bank)
  /-- 船に乗っている -/
  | boat
deriving Inhabited, BEq

/-- 人々の状態 -/
structure State where
  /-- 各人がいる場所 -/
  place : Person → Place

  /-- 船がどちらの岸にいるか -/
  boat : Bank
deriving Inhabited

/- これで、各時点での状態を表現することができました。初期状態とゴール状態を定義することができるか、確かめておきましょう。 -/

/-- 初期状態。全員こちら岸にいて、船もこちら岸にある -/
def initial : State :=
  { place := fun _ => Place.ofBank .here, boat := .here }

/-- ゴール状態。全員向こう岸にいて、船も向こう岸にある -/
def final : State :=
  { place := fun _ => Place.ofBank .there, boat := .there }

/- ## 状態の表示

このままだと `s : State` を見やすく表示する方法が存在せずデバッグに困るので、表示方法を指定しておきます。
-/

protected def Person.toString (p : Person) : String :=
  match p with
  | .man id => s!"🚹{id}"
  | .woman id => s!"🚺{id}"

instance : ToString Person := ⟨Person.toString⟩

protected def State.toString (s : State) : String :=
  -- こちら岸にいる人
  let peopleHere := people.filter (fun p => s.place p == .ofBank .here)
  -- 向こう岸にいる人
  let peopleThere := people.filter (fun p => s.place p == .ofBank .there)
  -- 船の位置と、船に乗っている人
  let peopleOnBoat := people.filter (fun p => s.place p == .boat)
  let boat :=
    match s.boat with
    | .here => s!"__{peopleOnBoat}🚢"
    | .there => s!"🚢{peopleOnBoat}__"
  s!"{peopleThere}{boat}{peopleHere}"

instance : ToString State := ⟨State.toString⟩

/-- info: "[]__[]🚢[🚹0, 🚹1, 🚹2, 🚺0, 🚺1, 🚺2]" -/
#guard_msgs in --#
#eval toString initial

/-- info: "[🚹0, 🚹1, 🚹2, 🚺0, 🚺1, 🚺2]🚢[]__[]" -/
#guard_msgs in --#
#eval toString final

/- ## 状態の遷移

次は、各状態から「どの状態へは１ステップで遷移できて、どの状態へはできないのか」を表現したいですね。それができれば、状態遷移のグラフが得られたことになり、そのグラフを **幅優先探索(breadth first search)** すれば、初期状態からゴール状態までの最短経路が求まるからです。

まず、ある状態が問題文の条件を満たしているかどうかを判定する関数を用意しましょう。
-/

/-- 状態が問題文の条件を満たす。
* 船には２人までしか乗っていない
* すべての女性は「自分の夫と一緒にいるか、あるいはどの男性とも一緒にいない」 -/
def State.isValid (s : State) : Bool :=
  let boatCond : Bool := people
    |>.filter (fun p => s.place p == .boat)
    |> (List.length · ≤ 2)
  let womenCond : Bool :=
    women.all (fun w =>
      s.place w == s.place w.spouse || -- 自分の夫と一緒にいる
      men.all (fun m => s.place m != s.place w) -- どの男性とも一緒にいない
    )
  boatCond && womenCond

-- テスト。初期状態とゴール状態は条件を満たす
#guard initial.isValid
#guard final.isValid

/- 以降、問題文にある「嫉妬深い夫の嫉妬を受けないという条件」を満たすことを単に「妥当である」ということにします。 -/

/-
次に、ある状態から１ステップで遷移できる状態を全列挙する関数を用意しましょう。１ステップでできることというのは、次の３通りですね。

* 船に乗っている人を１人岸に下ろす
* 岸にいる人を１人船に乗せる
* 誰かが船を漕いで対岸に移動させる

(船に２人乗せるのは、１人乗せるのを繰り返せば実現できるのでここでは１ステップと認めないことにしました)
-/

/-- `p` さんの乗船状態をトグルして新しい状態を得る。
`p` さんが乗船済みであれば降ろし、`p` さんが岸にいるなら船に乗せる。

以下の場合は失敗して `none` を返す
* `p` さんがいる岸に船が停泊していない場合。
* 得られた状態が妥当な状態ではない場合。
-/
def State.putOff (s : State) (p : Person) : Option State :=
  let candidate? : Option State :=
    match s.place p with
    -- p さんが船に乗っている場合
    | .boat =>
      let newPlace : Person → Place := fun x =>
        if x == p then
          -- p さんを船から降ろす
          .ofBank s.boat
        else
          -- 他の人はそのまま
          s.place x
      some { s with place := newPlace }

    -- p さんが岸にいる場合
    | .ofBank bank =>
      if bank != s.boat then
        -- p さんがいる岸に、船が停まっていない場合は、乗れない
        none
      else
        let newPlace : Person → Place := fun x =>
          if x == p then
            -- p さんを船に乗せる
            .boat
          else
            -- 他の人はそのまま
            s.place x
        some { s with place := newPlace }
  match candidate? with
  | .some state =>
    if state.isValid then some state else none
  | .none => none

/-- 対岸を取得する -/
def Bank.toggle (b : Bank) : Bank :=
  match b with
  | .here => .there
  | .there => .here

/-- 船を対岸に移動させる。
ただし、誰かが船に乗っていなければ失敗して `none` を返す -/
def State.boatTrip (s : State) : Option State :=
  if people.any (fun p => s.place p == .boat) then
    some { s with boat := s.boat.toggle }
  else
    none

/-- ある状態から、次に１ステップで遷移可能な状態を全列挙する。
返り値のリストに含まれる状態 `s` は、すべて妥当な状態でなければいけない。
-/
def State.nextStates (s : State) : List State :=
  people
    |>.map (State.putOff s ·)
    |> (s.boatTrip :: ·)
    |>.reduceOption

/- ## 幅優先探索

後は、予告したように幅優先探索を行います。

幅優先探索は、グラフを探索してあるノードから別のノードへの最短経路を求めるためによく用いられるアルゴリズムです。幅優先探索は、グラフを探索しながら「次に訪れるべきノード」を何かしらのキューに保存していくことによって実装できます。Lean では [`Std.Queue`](#{root}/Type/Queue.md) が標準的なキューの実装として用意されているので、それを使います。

話をできるだけ一般的にするために、ここでは `Graph` という型クラスを定義しておいて、それに対して幅優先探索アルゴリズムを実装します。
-/

class Graph (α : Type) where
  /-- ノード `v` に隣接しているノードのリストを返す -/
  neighbors : α → List α

variable {α : Type} [BEq α] [Hashable α]

open Std

/-- あるノード `s` から始めて、ノード `t` に到達するまでの幅優先探索を行う。
後で経路を復元するために、親ノードを記録した辞書を返す -/
def Graph.bfs [Graph α] (s t : α) : HashMap α α := Id.run do
  -- キューを空の状態で初期化
  -- このキューは「これから訪問するべきノード」を管理する
  let mut q : Queue α := ∅

  -- 親ノードを記録する辞書
  let mut parent : HashMap α α := ∅

  -- 訪問済みであるかどうか管理する集合
  let mut visited : HashSet α := ∅

  -- 初期ノードをキューに追加
  q := q.enqueue s
  visited := visited.insert s

  -- キューが空になるまでループ
  while !q.isEmpty do
    -- キューからノードを取り出す
    let some (v, q') := q.dequeue? | unreachable!
    q := q'

    -- 目的のノードに出会ったら探索を終了する
    if v == t then
      break

    for u in Graph.neighbors v do
      if u ∉ visited then
        visited := visited.insert u
        parent := parent.insert u v
        q := q.enqueue u

  return parent

/-- グラフの親を記録した辞書から、ノード `t` への経路を復元する -/
def constructPath (parent : HashMap α α) (t : α) : List α := Id.run do
  let mut path : List α := []
  let mut cur? : Option α := t

  while cur?.isSome do
    let some cur := cur? | unreachable!
    path := cur :: path
    cur? := parent[cur]?

  path

/-- 幅優先探索によって、ノード `s` からノード `t` への最短パスを求める -/
def Graph.findShortestPath [Graph α] (s t : α) : List α :=
  let parent := Graph.bfs s t
  constructPath parent t

/-
## 探索の実行

後は、`State` に対して幅優先探索を実行しましょう。まず、`Graph` のインスタンスにします。
-/

instance : Graph State where
  neighbors := State.nextStates

/- 次に `BEq` のインスタンスにします。 -/

/-- 2つの状態が等しいかどうかを判定する -/
def State.beq (s1 s2 : State) : Bool :=
  s1.boat == s2.boat && people.all (fun p => s1.place p == s2.place p)

/-- `==` という記号が使えるようにする -/
instance : BEq State := ⟨State.beq⟩

/- 経路を出力するために辞書を使う関係で、`Hashable` のインスタンスも必要です。 -/

deriving instance Hashable for Bank, Place

protected def State.hash (s : State) : UInt64 :=
  let places := .ofBank s.boat :: people.map s.place
  Hashable.hash places

instance : Hashable State := ⟨State.hash⟩

/- 以上の準備の下で、計算を実行することができます。やってみるとパスが見つかるので、全員が川を渡ることは可能であることがわかります。 -/

open Std

/--
info:
[]__[]🚢[🚹0, 🚹1, 🚹2, 🚺0, 🚺1, 🚺2]
[]__[🚺0]🚢[🚹0, 🚹1, 🚹2, 🚺1, 🚺2]
[]__[🚹0, 🚺0]🚢[🚹1, 🚹2, 🚺1, 🚺2]
[]🚢[🚹0, 🚺0]__[🚹1, 🚹2, 🚺1, 🚺2]
[🚹0]🚢[🚺0]__[🚹1, 🚹2, 🚺1, 🚺2]
[🚹0]__[🚺0]🚢[🚹1, 🚹2, 🚺1, 🚺2]
[🚹0]__[🚺0, 🚺1]🚢[🚹1, 🚹2, 🚺2]
[🚹0]🚢[🚺0, 🚺1]__[🚹1, 🚹2, 🚺2]
[🚹0, 🚺0]🚢[🚺1]__[🚹1, 🚹2, 🚺2]
[🚹0, 🚺0]__[🚺1]🚢[🚹1, 🚹2, 🚺2]
[🚹0, 🚺0]__[🚹1, 🚺1]🚢[🚹2, 🚺2]
[🚹0, 🚺0]🚢[🚹1, 🚺1]__[🚹2, 🚺2]
[🚹0, 🚹1, 🚺0]🚢[🚺1]__[🚹2, 🚺2]
[🚹0, 🚹1, 🚺0]__[🚺1]🚢[🚹2, 🚺2]
[🚹0, 🚹1, 🚺0]__[🚺1, 🚺2]🚢[🚹2]
[🚹0, 🚹1, 🚺0]🚢[🚺1, 🚺2]__[🚹2]
[🚹0, 🚹1, 🚺0, 🚺1]🚢[🚺2]__[🚹2]
[🚹0, 🚹1, 🚺0, 🚺1]__[🚺2]🚢[🚹2]
[🚹0, 🚹1, 🚺0, 🚺1]__[🚹2, 🚺2]🚢[]
[🚹0, 🚹1, 🚺0, 🚺1]🚢[🚹2, 🚺2]__[]
[🚹0, 🚹1, 🚹2, 🚺0, 🚺1]🚢[🚺2]__[]
[🚹0, 🚹1, 🚹2, 🚺0, 🚺1, 🚺2]🚢[]__[]
-/
#guard_msgs (whitespace := lax) in --#
#eval show IO Unit from do
  let path := Graph.findShortestPath initial final
  for p in path do
    IO.println p
