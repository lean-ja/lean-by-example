import Lean --#
/- # Subtype

`Subtype` は、大雑把に言えば型 `A : Type` の部分集合を表します。すなわちある述語 `p : A → Prop` があったとき、`Subtype p` は `A` の項であって `p` という性質を満たすようなものの全体を表します。
-/

-- 正の数を表す subtype
#check Subtype (fun n => n > 0)

/- `{x // p x}` という専用の構文が用意されていて、これで `Subtype` を表すことができます。 -/

-- 正の数を表す subtype
#check { n : Nat // n > 0 }

/- ## 用途

`Subtype` を使うと、ある型 `A` が `U` という型の一部を切り取ったものだということをコードで表現することができます。たとえば、自然数の型 `Nat` に対して、正の数だけを抜き出して正の整数の型 `Pos` を定義することを考えてみます。

このとき、`Subtype` を使わずに `Pos` を帰納型として以下のように定義することもできるのですが、こうすると `Pos` と `Nat` は実装上まったく無関係ということになってしまいます。
-/
namespace Hidden --#

inductive Pos where
  | one
  | succ (n : Pos)

end Hidden --#
/- その結果、`Nat` に対するコンパイラ上の演算の最適化の恩恵を受けることができなくなり、たとえば足し算が非常に遅くなります。 -/

open Lean Elab Command in

/-- 2つのコマンドのうち最初のコマンドのほうが `n` 倍早く終わることを確かめるコマンド -/
elab "#speed_rank " "|" stx1:command "|" stx2:command "ratio" n:num : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx1
  let end_time ← IO.monoMsNow
  let time1 := end_time - start_time

  let start_time ← IO.monoMsNow
  elabCommand stx2
  let end_time ← IO.monoMsNow
  let time2 := end_time - start_time

  logInfo m!"runnning time of fst command: {time1}ms"
  logInfo m!"runnning time of snd command: {time2}ms"

  let n := n.getNat
  -- 最初のコマンドが２つめのコマンドより早く終わっているか検証する
  unless time1 * n < time2 do
    throwError m!"fst command is slower than snd command."

namespace Inductive
  /- ## 別の帰納型として正の整数を定義する -/

  inductive Pos where
    | one
    | succ (n : Pos)

  def Pos.ofNat (n : Nat) : Pos :=
    match n with
    | 0 => Pos.one
    | 1 => Pos.one
    | n + 2 => Pos.succ (Pos.ofNat n)

  instance (n : Nat) : OfNat Pos (n + 1) where
    ofNat := Pos.ofNat n

  def Pos.add (m n : Pos) : Pos :=
    match n with
    | Pos.one => Pos.succ m
    | Pos.succ n' => Pos.succ (Pos.add m n')

  instance : Add Pos where
    add := Pos.add

end Inductive

namespace Subtype
  /- ## Subtype として正の整数を定義する -/

  def Pos := { n : Nat // n > 0 }

  def Pos.ofNat (n : Nat) : Pos :=
    ⟨n + 1, Nat.succ_pos n⟩

  instance (n : Nat) : OfNat Pos (n + 1) where
    ofNat := Pos.ofNat n

  def Pos.add (m n : Pos) : Pos :=
    ⟨m.val + n.val, by
      have mp := m.property
      have np := n.property
      omega
    ⟩

  instance : Add Pos where
    add := Pos.add

end Subtype

-- 5倍以上も遅くなってしまう
#speed_rank
  | #reduce (500 : Subtype.Pos) + (500 : Subtype.Pos)
  | #reduce (500 : Inductive.Pos) + (500 : Inductive.Pos) ratio 5
