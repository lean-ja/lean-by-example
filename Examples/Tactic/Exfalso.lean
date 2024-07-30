/- # exfalso
`exfalso` はゴールを矛盾を意味する `False` に換えます。

「矛盾からはどんな命題でも示せる」という命題 `False → P` のことを爆発律(principle of explosion)といいますが、これはラテン語で ex falso と呼ばれるようで、これが名前の由来のようです。

仮定の中に矛盾があるとき、ゴールが具体的に何であるかは関係がないので、`exfalso` を使ってゴールを `False` に変えた方が分かりやすいでしょう。
-/

variable (P Q : Prop)

example (h : P) (hn : ¬ P) : P ∧ Q := by
  -- 仮定の中に矛盾があるので、ゴールが何であるかは関係ない
  -- なので、ゴールを `False` に変える
  exfalso
  show False

  exact hn h

/- ローカルコンテキスト内に `P` と `¬ P` があって矛盾することを指摘したい場合は、[`contradiction`](./Contradiction.md) を使うとより簡潔です。また、一般に問題が命題論理に帰着されている状況では [`tauto`](./Tauto.md) または [`itauto`](./Itauto.md) が利用できます。-/

/- ## 舞台裏
矛盾つまり `False` の項からはどんな命題でも示せるというのは最初は奇妙に感じるかもしれません。実際に `False` の構成を真似て自分で帰納型を定義することによって、同様のことを再現できます。
-/

universe u

-- まずコンストラクタを持たない帰納型を定義する
-- これで False を模倣したことになる
inductive MyFalse : Prop

-- 帰納型を定義すると、再帰子(recursor)が自動生成される
-- 再帰子は数学的帰納法の原理に相当する
-- MyFalse の再帰子は以下のようになる
-- 再帰子によって、MyFalse からの関数を定義することができる
#check (@MyFalse.rec : (motive : MyFalse → Sort u) → (t : MyFalse) → motive t)

-- motive の返り値の型の Sort u には Prop も含まれる
-- したがって `fun _ => P` という関数を再帰子に渡すことができて証明ができる
example (h : MyFalse) : P := @MyFalse.rec (fun _ => P) h
