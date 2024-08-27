/- # 床屋のパラドックス
集合論が提唱された当初、任意の述語 `P` に対して `P` を満たす要素の集合 `{ x | P x }` が存在するとされていました。このルールを内包公理と呼びます。`P` が成り立つ要素を集めてくることができると主張しているわけで、直観的で受け入れやすいと思われます。しかし、特に述語 `P` として「自分自身を含まない」という述語を採用すると、矛盾が生じることが知られています。これは Russel のパラドックスと呼ばれています。

この問題を回避する方法は複数ありえますが、現在広く採用されている ZFC 集合論では、内包公理の適用範囲を部分集合に限定して主張を弱めることで Russel のパラドックスを回避しています。

以上が Russel のパラドックスの概要です。床屋のパラドックスとは、Russel のパラドックスの内容をわかりやすく説明するために考えられた比喩です。

その内容は自然言語では次のように説明できます。

```admonish info title=""
ある村に床屋がいます。その床屋は、自分で髭を剃る村人の髭は剃らず、自分で髭を剃らない村人の髭を剃るという信念を持っています。このとき、その床屋は自分の髭を剃るでしょうか？

仮に剃るとしたら、その床屋はまさに「自分で自分の髭を剃っている」ので剃ってはならないはずで、矛盾が生じます。逆に剃らないとすると、その床屋はまさに「自分で自分の髭を剃らない」ので自分の髭を剃らなければならないことになり、矛盾が生じます。

いずれにせよ矛盾が生じてしまうので、そんな床屋は存在しません！
```

この内容を Lean で表現してみましょう。演習問題として、`sorry` の部分を埋めてみてください。
-/
namespace Barber
set_option autoImplicit false --#

/-- 全体集合となる人々の集合 -/
opaque Person : Type

/-- p さんが q さんの髭を剃るという述語 -/
opaque shave (p q : Person) : Prop

-- 床屋が存在するという仮定
variable (barber : Person)

-- 床屋の信念を仮定として表現したもの
variable (policy : ∀ p : Person, shave barber p ↔ ¬ shave p p)

example : False := by
  sorry

end Barber
