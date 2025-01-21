/- # push_cast

`push_cast` タクティクは、ゴールや仮定に含まれる[型強制](#{root}/TypeClass/Coe.md)を「内側へ押し込む」はたらきをします。
-/
import Mathlib.Tactic

example (m n : ℕ) (h : m ≥ n) : n + ((m - n) : ℕ) = (m : ℤ) := by
  -- 示すべき命題には `m - n : ℕ` を整数 `ℤ` に型キャストしたものが含まれている。
  guard_target =ₛ ↑n + ↑(m - n) = (m : ℤ)

  -- この状態では整数と自然数の演算が混ざっていてややこしいので、
  -- `ring` だけで示すことはできない。
  fail_if_success solve
  | ring

  -- 自然数の引き算は整数での引き算とは異なる定義がされているが、
  -- この場合は `h : m ≥ n` という仮定があるので、`m - n : ℤ` と一致する。
  -- この変換を `push_cast` タクティックで行うことができる。
  push_cast [h]

  -- 型キャストが「内側に押し込まれ」て、整数の話になった。
  show ↑n + (↑m - ↑n) = (m : ℤ)

  -- `ring` で示せるようになった！
  ring

/- [`norm_cast`](./NormCast.md) や [`zify`](./Zify.md) などの型キャスト系のタクティクと併用されることもあります。-/

example (m n : ℕ) (h : n ≥ m) : (n + m) * (n - m) = n * n - m * m := by
  -- 整数にキャストする
  zify

  -- 自然数の引き算が含まれているので、`ring` では示せない
  fail_if_success solve
  | ring

  -- 仮定 `h : n ≥ m` を使って、`n - m` と `n * n - m * m` を整数にキャストする
  push_cast [h, show n * n ≥ m * m from by bound]

  -- `ring` で示せるようになった！
  ring
