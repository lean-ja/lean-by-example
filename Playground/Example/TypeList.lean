/-
`[(Nat, 1), (String, "hello"), (Bool, true)]` のようなリストに対する適切な型はなんだろう？
-/

def sampleList : List ((α : Type) × α) :=
  [⟨Nat, 1⟩, ⟨String, "hello"⟩, ⟨Bool, true⟩]
