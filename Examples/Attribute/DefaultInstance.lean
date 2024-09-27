/- # default_instance

`[default_instance]` 属性は、型クラス解決が（型情報の不足などで）上手くいかない場合に、最後の手段としてインスタンス解決に使われるインスタンスを指定します。
-/

-- `Int` は `Mul` 型クラスのインスタンスで、
-- インスタンス名は `Int.instMul`
#check (Int.instMul : Mul Int)

-- `x, y` の型がわからないので `x * y` をどう解釈すればいいか Lean はわからない
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  HMul (?m.27 y) ?m.18 (?m.28 y x)
-/
#guard_msgs in
  #reduce fun y => (fun x => x * y)

-- `y` の型を明示的に与えればエラーは消える
#reduce fun (y : Nat) => (fun x => x * y)

-- `Mul` のインスタンスを探して見つからなかった際に `Int.instMul` を使うように指定する
attribute [default_instance] Int.instMul

-- エラーが消えた！
#reduce fun y => (fun x => x * y)

/- ## 用途
典型的な使用方法は、[`OfNat`](../TypeClass/OfNat.md) 型クラスの（型を指定しない場合の）解釈のされ方を変更することでしょう。
-/

/-- 自然数の対 -/
def NatPair := Nat × Nat

/-- `(0, 0)` を単に `0 : NatPair` と書けるようにする -/
instance instNatPair : OfNat NatPair 0 := ⟨(0, 0)⟩

-- 期待される型を指定しない場合、数値リテラルは `Nat` の項であると解釈される
/-- info: 0 : Nat -/
#guard_msgs in #check 0

-- 期待される型を指定しなければ、数値リテラルを `NatPair` の項として解釈する
attribute [default_instance] instNatPair

-- `NatPair` の項として解釈されるようになった！
/-- info: 0 : NatPair -/
#guard_msgs in #check 0

-- 期待される型を指定したときの挙動は変わらない。
-- 相変わらず `Nat` の項として解釈される
/-- info: 0 : Nat -/
#guard_msgs in #check (0 : Nat)

/- ## インスタンス優先度との違い

インスタンス優先度(priority)という機能もあります。これも型クラス解決の優先度に関係する機能ですが、`[default_instance]` 属性とは挙動が異なります。Lean はインスタンス解決の際にまずインスタンス優先度の高いものから試し、すべて失敗した場合にのみ `[default_instance]` 属性を参照します。つまり、考慮される順番が異なるということです。
-/

/-- ⋄ 記法のための型クラス -/
class Diamond (α : Type) where
  dia : α

notation "⋄" => Diamond.dia

/-- `⋄ : Nat` が `0` を表すものとする -/
instance instDiaZero : Diamond Nat where
  dia := 0

/-- `⋄ : Nat` が `1` を表すものとする -/
instance instDiaOne : Diamond Nat where
  dia := 1

-- 二つのインスタンスが衝突しているが、
-- 後に定義された方が優先される
#guard (⋄ : Nat) = 1

-- `0` と解釈する方をデフォルトにする
attribute [default_instance] instDiaZero

-- デフォルトインスタンスにしても効果がなく、相変わらず `1` の方が優先される！
-- これは、期待される型がわかっていて型クラス解決が早期に成功するから
#guard (⋄ : Nat) = 1

-- 期待される型が不明な状況であれば、
-- デフォルトインスタンスが使用される
/-- info: 0 -/
#guard_msgs in #eval ⋄

/-- `⋄ : Nat` が `2` を表すものとする。優先度を `high` にしておく -/
instance (priority := high) instDiaTwo : Diamond Nat where
  dia := 2

/-- `⋄ : Nat` が `3` を表すものとする -/
instance instDiaThree : Diamond Nat where
  dia := 3

-- `2` と解釈する方が優先されるようになった！
#guard (⋄ : Nat) = 2
