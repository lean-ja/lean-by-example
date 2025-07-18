import Batteries

/-- アルファベットの小文字 -/
abbrev LowerLetter := { c : Char // c.isLower }


namespace LowerLetter
  -- ## `UInt32` への変換を行う関数

  /-- 範囲証明付きの`UInt32`への変換 -/
  def toUInt32ₛ (c : LowerLetter) : { u : UInt32 // u ≥ 97 && u ≤ 122 } :=
    ⟨Char.val c, by
      have := c.property
      simp_all [Char.isLower]
    ⟩

  /-- 範囲証明なしの`UInt32`への変換 -/
  def toUInt32 (c : LowerLetter) : UInt32 :=
    Char.val c

end LowerLetter


#eval (3 : UInt32) % 2

namespace LowerLetter
  -- ## `UInt32` から `LowerLetter` への変換を行う関数

  private def _root_.Char.ofUInt32? (u : UInt32) : Option Char :=
    if h : u.isValidChar then some ⟨u, h⟩ else none

  private def ofChar? (c : Char) : Option LowerLetter :=
    if h : c.isLower then some ⟨c, h⟩ else none

  /-- `UInt32`から`LowerLetter`への変換 -/
  def ofUInt32? (u : UInt32) : Option LowerLetter := do
    let char ← Char.ofUInt32? u
    ofChar? char

  /-- `UInt32`から`LowerLetter`への範囲証明付きの変換 -/
  def ofUInt32 (u : UInt32) (hu : u ≥ 97 && u ≤ 122) : LowerLetter :=
    let char : Char := ⟨u, by
      replace hu : 97 ≤ u.toNat ∧ u.toNat ≤ 122 := by simpa using hu
      suffices goal : u.toNat < 55296 ∨ 57343 < u.toNat ∧ u.toNat < 1114112 from by
        simp_all [UInt32.isValidChar, Nat.isValidChar]
      omega
    ⟩
    ⟨char, by dsimp [Char.isLower]; exact hu⟩

end LowerLetter


namespace LowerLetter
  -- ## `LowerLetter` と `Nat` の相互変換

  /-- 単なる`Nat`への変換 -/
  def toNat (c : LowerLetter) : Nat :=
    c.val.toNat

  /-- 範囲証明付の`Nat`への変換 -/
  def toNatₛ (c : LowerLetter) : { n : Nat // n ≥ 97 && n ≤ 122 } :=
    ⟨c.val.toNat, c.property⟩

  private def _root_.Char.ofNat? (n : Nat) : Option Char :=
    if h : (n.toUInt32).isValidChar then some ⟨n.toUInt32, h⟩ else none

  /-- `Nat`から`LowerLetter`への変換 -/
  def ofNat? (n : Nat) : Option LowerLetter := do
    let char ← Char.ofNat? n
    ofChar? char

  example (u v : UInt32) : u ≤ v ↔ u.toNat ≤ v.toNat := by
    exact UInt32.le_iff_toNat_le

  example (u v : UInt32) : u ≥ v ↔ u.toNat ≥ v.toNat := by
    exact UInt32.le_iff_toNat_le

  set_option warn.sorry false in --#

  /-- `Nat`から`LowerLetter`への範囲証明付きの変換 -/
  def ofNat (n : Nat) (hn : n ≥ 97 && n ≤ 122) : LowerLetter := by
    replace hn : 97 ≤ n ∧ n ≤ 122 := by simpa using hn
    dsimp [LowerLetter]
    let u := UInt32.ofNatLT n (by simp only [UInt32.size]; omega)
    have hu : u ≥ 97 && u ≤ 122 := by
      simp [u]

      sorry
    sorry

end LowerLetter
