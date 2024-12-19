/- # contradiction

矛盾からはどんな命題でも証明することができます。これを爆発律(principle of explosion)と呼びますが、`contradiction` は、この爆発律を使ってゴールを閉じるタクティクです。

ローカルコンテキストに `P` と `¬ P` が同時にあるなど、矛盾した状況にあるときにゴールを閉じます。
-/
import Mathlib.Algebra.Algebra.Basic -- `not_lt` などが使えるようにする

variable (P Q : Prop)

-- `False`
example (h : False) : P := by contradiction

-- 明らかに偽な等式
example (h : 2 + 2 = 3) : P := by contradiction

-- 明らかに偽な等式
example (x : Nat) (h : x ≠ x) : P := by contradiction

-- 矛盾する仮定
example (hP : P) (hnP : ¬ P) : Q := by contradiction

/- 爆発律を利用するタクティクには他に [`exfalso`](./Exfalso.md) もありますが、あちらはゴールを `False` に書き換えるだけで、ゴールを閉じるところまでは行いません。-/

/- ## 補足
以下の例では、`contradiction` がいかにも通りそうに見えるのですが、通りません。`contradiction` にはあまり強力な前処理は備わっていないので、注意が必要です。
-/

variable (n m : ℕ)

example (hl : n ≤ m) (hg : m < n) : False := by
  -- 明らかに矛盾に見えるが、 通らない
  fail_if_success contradiction

  -- 通らない理由は、 `n ≤ m` が `¬ m < n` を意味することを
  -- `contradiction` は知らないから。

  -- 次のようにして教えてあげると…
  have := hl.not_lt

  -- `contradiction` が通るようになる
  contradiction
