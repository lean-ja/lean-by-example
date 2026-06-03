/- # 嫉妬深い夫たちの川渡りパズル

**嫉妬深い夫の問題(Jealous Husbands Problem)** と呼ばれる、以下の古典的なパズルを Lean で解いてみましょう。

> 3 組の夫婦が川を渡らなければならない。船が一隻あるが、一度に２人までしか乗ることができない。
>
> さらに、どの男性も大変嫉妬深いので、自分がいないときに自分の妻と他の男性が一緒にいることを許さない。
> 川のこちら側の岸にいるときも、向こう岸にいるときも、船に乗っているときも、常に女性は「自分の夫と一緒にいるか、あるいはどの男性とも一緒にいない」ことが必要である。
>
> この条件のもとで全員が川を渡って向こう岸に辿り着くことはできるだろうか？

-/

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

/- ## 状態の遷移

次は、各状態から「どの状態へは１ステップで遷移できて、どの状態へはできないのか」を表現したいですね。それができれば、状態遷移のグラフが得られたことになり、そのグラフを **幅優先探索(breadth first search)** すれば、初期状態からゴール状態までの最短経路が求まります。

まず、ある状態が問題文の条件を満たしているかどうかを判定する関数を用意しましょう。
-/

/-- 状態が問題文の条件を満たす。
すなわち、すべての女性は「自分の夫と一緒にいるか、あるいはどの男性とも一緒にいない」 -/
def State.isValid (s : State) : Bool :=
  let women := [0, 1, 2].map Person.woman
  let men := [0, 1, 2].map Person.man
  women.all (fun w =>
    s.place w == s.place w.spouse || -- 自分の夫と一緒にいる
    men.all (fun m => s.place m != s.place w) -- どの男性とも一緒にいない
  )

-- テスト。初期状態とゴール状態は条件を満たす
#guard initial.isValid
#guard final.isValid

/-
次に、ある状態から１ステップで遷移できる状態を全列挙する関数を用意しましょう。１ステップでできることというのは、

* 船に乗っている人を１人岸に下ろす
* 船に乗っている人を２人岸に下ろす
* 岸にいる人を１人船に乗せる
* 岸にいる人を２人船に乗せる
* 船を岸から岸へ移動させる
-/
