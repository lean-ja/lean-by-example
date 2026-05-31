import LeanByExample.Lib.SpeedRank --#

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

-- 帰納型として定義すると5倍以上も遅くなってしまう
#reduce (500 : Subtype.Pos) + (500 : Subtype.Pos)
#reduce (500 : Inductive.Pos) + (500 : Inductive.Pos)
--#--
#speed_rank (ratio := 5)
  | #reduce (500 : Subtype.Pos) + (500 : Subtype.Pos)
  | #reduce (500 : Inductive.Pos) + (500 : Inductive.Pos)
--#--
