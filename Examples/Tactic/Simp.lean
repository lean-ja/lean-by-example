/- # simp

`simp` は，ターゲットを決められた規則に基づいて自動で簡約（simplify）するタクティクです．カスタマイズすることが可能で，簡約に使ってほしい命題を登録することができます．-/

universe u v

-- 圏の公理
class Category (C : Type u) where
  -- 射
  Hom : C → C → Type v

  -- 射の合成
  comp : ∀ {a b c : C}, Hom a b → Hom b c → Hom a c

  -- 恒等射. `id a` が `a` 上の恒等射を意味する
  id : ∀ (a : C), Hom a a

  -- 恒等射の性質
  id_comp : ∀ {a b : C} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : C} (f : Hom a b), comp f (id b) = f

  -- 射の結合律
  assoc : ∀ {a b c d : C} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

-- `f : Hom a b`と`g : Hom b c`の合成を`f ≫ g`と書く
infixr:80 " ≫ " => Category.comp

-- `Category.hoge` ではなく `hoge` で呼び出せるようにする
open Category

-- 公理の等式が `simp` で使えるようにする
attribute [simp] id_comp comp_id assoc

-- 変数の定義
variable {C : Type u} [Category.{u, v} C] {a b c d e : C}

example (f : Hom a b) (g : Hom b c) (h : Hom c d) (i : Hom d e) :
    (f ≫ (id b ≫ g)) ≫ (h ≫ i) = f ≫ (g ≫ ((id c ≫ h) ≫ i)) := by
  -- 上で `simp` で使えるようにした等式を使って自動で簡約する
  simp

/-! 既知の `h : P` という証明を使って簡約させたいときは，明示的に `simp [h]` と指定することで可能です．

何も指定しなければゴールを簡約しますが，ローカルコンテキストにある `h : P` を簡約させたければ `simp at h` と指定することで可能です．

## simp?

`simp` は自動的に証明を行ってくれますが，何が使われたのか知りたいときもあります．`simp?` は簡約に何が使われたのかを示してくれるので，`rw` などを用いて明示的に書き直すことができます．

## simp_all

`simp_all` は `simp [*] at *` の強化版で，ローカルコンテキストとゴールをこれ以上簡約できなくなるまですべて簡約します．

## dsimp

`dsimp` は，定義上(definitionally)等しいもの同士しか簡約しないという制約付きの `simp` です．-/
