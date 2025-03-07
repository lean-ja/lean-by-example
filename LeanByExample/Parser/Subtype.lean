/- # 部分型構文

`{x : T // p x}` は、[部分型](#{root}/Type/Subtype.md)を表す構文です。
-/

/-⋆-//-- info: { x // x > 0 } : Type -/
#guard_msgs in --#
#check { x : Int // x > 0 }

/- もしこの構文がなければ、`Subtype` を定義するには以下のように書く必要があります。 -/

/-- 標準の `Subtype` を真似て自前で定義した型 -/
structure MySubtype {α : Type} (p : α → Prop) where
  val : α
  property : p val

-- 正の自然数全体を表す部分型
#check MySubtype (fun x : Nat => x > 0)

/- しかし、この構文があるおかげで、次のように見やすく簡潔に書くことができます。 -/

@[inherit_doc MySubtype] syntax "my{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `(my{ $x : $type // $p }) => ``(MySubtype (fun ($x:ident : $type) => $p))
  | `(my{ $x // $p }) => ``(MySubtype (fun ($x:ident : _) => $p))

-- 正の自然数全体を表す部分型
#check my{ x // x > 0 }
