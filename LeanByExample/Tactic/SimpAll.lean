/- # simp_all

`simp_all` タクティクは、[`simp`](#{root}/Tactic/Simp.md) タクティクの派生で、仮定とゴールに対してこれ以上適用できなくなるまで `simp` を適用します。

## `simp [*] at *` との違い

`simp [*] at *` と似ていますが、`simp_all` は単純化された仮定を再び単純化に使うという、再帰的な挙動をします。
-/

example (P : Nat → Bool)
    (h1 : P (if 0 + 0 = 0 then 1 else 2))
    (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
  -- `simp [*] at *` では示せない
  fail_if_success solve
  | simp [*] at *

  -- 複数回 `simp [*] at *` を繰り返す必要がある
  simp [*] at *
  simp [*] at *
  simp [*] at *

example (P : Nat → Bool)
    (h1 : P (if 0 + 0 = 0 then 1 else 2))
    (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
  -- 一発で終わる。
  -- h1 を単純化した後で、h2 を「単純化後の h1」を使って単純化し、
  -- さらにゴールを単純化するという挙動をする。
  simp_all

/- ## 注意点

なお、これは `simp [*] at *` と同じですが `simp_all` はローカルコンテキストにある命題を使って単純化を行おうとするため、ローカルコンテキストにある命題によってはエラーになることがあります。[^bad_simp] -/

example (_h : 1 + 1 = 2) : True := by
  have : 1 = 1 + 1 - 1 := by simp

  -- `simp_all` では示せない
  -- 仮定にある `1` を `1 + 1 - 1` に置き換えて無限ループになっているようだ
  fail_if_success solve
  | simp_all

  -- `simp [*] at *` でも示せない
  fail_if_success solve
  | simp [*] at *

  trivial

example (_h : 1 + 1 = 2) : True := by
  -- 左辺と右辺を逆にしてみると
  have : 1 + 1 - 1 = 1 := by simp

  -- `simp_all` で示せるようになる
  simp_all

/- [^bad_simp]: ここで挙げているコード例は、Lean の公式 Zulip の aesop with a "bad simp hypothesis" in the context というスレッドで [Frédéric Dupuis さんが挙げたコード例](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/aesop.20with.20a.20.22bad.20simp.20hypothesis.22.20in.20the.20context/near/493137167)を参考にしています。-/
