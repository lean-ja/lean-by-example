/- # simp_all

`simp_all` タクティクは、[`simp`](#{root}/Tactic/Simp.md) タクティクの派生で、仮定とゴールに対してこれ以上適用できなくなるまで `simp` を適用します。

`simp at *` と似ていますが、`simp_all` は簡約された仮定を再び簡約に使うなど再帰的な挙動をします。
-/
section
  /- ## simp_all では示せるが simp at * では示せない例 -/

  example (P : Nat → Bool)
      (h1 : P (if 0 + 0 = 0 then 1 else 2))
      (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
    simp at *

    -- まだゴールが残っている
    show P 0

    simp [h1] at h2
    assumption

  example (P : Nat → Bool)
      (h1 : P (if 0 + 0 = 0 then 1 else 2))
      (h2 : P (if P 1 then 0 else 1) ) : P 0 := by
    -- 一発で終わる。
    -- h1 を簡約した後で、h2 を「簡約後の h1」を使って簡約し、
    -- ゴールと仮定が一致していることを確認するという挙動をする。
    simp_all
end
/- なお `simp_all` はローカルコンテキストにある命題を使って単純化を行おうとするため、ローカルコンテキストにある命題によってはエラーになることがあります。[^bad_simp]-/

/-⋆-//--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in --#
example (_h : 1 + 1 = 2) : True := by
  have : 1 = 1 + 1 - 1 := by simp

  -- `simp_all` では示せない
  -- 仮定にある `1` を `1 + 1 - 1` に置き換えて無限ループになっているようだ
  simp_all

example (_h : 1 + 1 = 2) : True := by
  -- 左辺と右辺を逆にしてみると
  have : 1 + 1 - 1 = 1 := by simp

  -- `simp_all` で示せるようになる
  simp_all

/- [^bad_simp] ここで挙げているコード例は、Lean の公式 Zulip の aesop with a "bad simp hypothesis" in the context というスレッドで [Frédéric Dupuis さんが挙げたコード例](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/aesop.20with.20a.20.22bad.20simp.20hypothesis.22.20in.20the.20context/near/493137167)を参考にしています。-/
