/- # Fin

`Fin n` は、「0 以上 n 未満」の自然数全体を表す型です。`Fin n` にはちょうど `n` 個の項があります。各項 `z : Fin n` は

* 値 `z.val : Nat` と、
* `z.val` が `n` 未満であることの証明 `z.isLt`

の組です。
-/

/-- `isLt` で `z.val` の値が `n` 未満であることの証明を取り出せる -/
example (z : Fin 5) : z.val < 5 := by
  exact z.isLt

/-- `Fin 3` には `0, 1, 2` に対応する３つの項がある -/
example (z : Fin 3) : z.val = 0 ∨ z.val = 1 ∨ z.val = 2 := by
  grind

/- ## 用途

### Lean に有限個しかないことを伝える

`Fin` 型は、例えば Lean に何かが「有限個しかない」ことを伝えたいときに役に立ちます。

例えば、「自明でない約数を持つ」という述語を考えてみます。
約数を探索すべき範囲が有限であるためこの述語は決定可能ですが、Lean はそれを自動的には認識しません。
-/

/-- 自然数 n は自明でない約数を持つ -/
def Nat.HasProperDivisor (n : Nat) : Prop :=
  ∃ m : Nat, m ∣ n ∧ 1 < m ∧ m < n

set_option warn.sorry false in --#

-- Decidable インスタンスの導出に失敗する
def instDecidableFail {n : Nat} : Decidable (Nat.HasProperDivisor n) := by
  unfold Nat.HasProperDivisor
  fail_if_success infer_instance
  sorry

/-
`∃ m : Nat` の部分を `Fin` で書き換えてやると、探索すべき範囲が有限であることが Lean に伝わるため、決定可能であることが自動的に導出できるようになります。
-/

/-- 自然数 n は自明でない約数を持つ(`Fin`で書き換えたバージョン) -/
def Nat.HasProperDivisorFin (n : Nat) : Prop :=
  ∃ m : Fin n, m.val ∣ n ∧ 1 < m.val

-- 決定可能性を自動的に導出できる
instance (n : Nat) : Decidable (Nat.HasProperDivisorFin n) := by
  unfold Nat.HasProperDivisorFin
  infer_instance

/- ### ちょうど n 個の要素を持つ型を作る

`Fin n` は「ちょうど `n` 個の要素を持つ型」として標準的なものなので、特定の個数の要素を持つ型を定義したいとき、`Fin` を使うと便利なことがあります。具体例としては [付録: 嫉妬深い夫たちの川渡りパズル](#{root}/EXTRA/Jealous.md) を参照してください。
-/
