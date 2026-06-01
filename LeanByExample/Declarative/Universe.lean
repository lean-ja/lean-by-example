/- # universe
`universe` は、宇宙レベルを表す変数を宣言するコマンドです。

ここで宇宙とは、項が再び型であるような型のことです。たとえば `Nat` や `Bool` は型ですが、Lean ではそのような型も項として扱われ、`Type` という宇宙に属しています。
-/

#check (Nat : Type)
#check (Bool : Type)

/- `Type` 自身も型ですが、`Type : Type` ではなく `Type : Type 1` です。`Type` は `Type 0` の略記で、`Type 0`, `Type 1`, `Type 2`, ... というように宇宙は階層になっています。 -/

#check (Type : Type 1)
#check (Type 1 : Type 2)

example : Type = Type 0 := rfl

/- ## 宇宙レベル変数

`Type u` の `u` は宇宙レベルを表す変数です。`universe u` と宣言すると、そのスコープ内で `u` を宇宙レベル変数として使えるようになります。
-/

section

universe u

#check (Type u : Type (u+1))

end

/- `u` は通常の変数ではなく、宇宙レベル専用の変数です。また、`variable` と同じくスコープに従うので、宣言していない場所では使えません。 -/

#check_failure (Type u)

/- ## 多相的な定義

`universe` で宣言した宇宙レベル変数を使うと、どの `Type u` にある型にも適用できる定義を書けます。次の `twice` は、`Nat : Type` にも `Type : Type 1` にも適用できます。
-/

section

universe u

def twice (α : Type u) : Type u := α × α

#check (twice : Type u → Type u)
#check (twice Nat : Type)
#check (twice Type : Type 1)

end

/- `universe` を使わず、定義名の後に `.{u}` を付けて宇宙変数を明示する書き方もあります。 -/

def twiceExplicit.{u} (α : Type u) : Type u := α × α

#check twiceExplicit

/- ## Type 1 が必要になる例

普通のデータだけをフィールドに持つ構造体は `Type` に属します。
-/

structure SmallConfig where
  retries : Nat
  verbose : Bool

#check (SmallConfig : Type)

/- 一方で、型そのものをデータとして保持したいことがあります。型のリストを作るだけでも、その型は `Type 1` に属します。 -/

#check ([Nat, Bool] : List Type)
#check (List Type : Type 1)

/- さらに、型とその型のサンプル値をひとまとめにしたレコードも考えてみます。 -/

structure SampleType where
  carrier : Type
  sample : carrier

def natSample : SampleType := { carrier := Nat, sample := 0 }
def boolSample : SampleType := { carrier := Bool, sample := true }

#check ([natSample, boolSample] : List SampleType)

/- この `SampleType` の項は `carrier : Type` というフィールドを持っています。つまり `SampleType` は `Type` 自身を要素として扱う型です。`Type : Type 1` なので、`SampleType` も `Type` ではなく `Type 1` に属します。 -/

#check (SampleType : Type 1)
#check_failure (SampleType : Type)

/- これが `Type 1` が単なる表示上の飾りではなく、実際に必要になる典型例です。型を値として格納したり、型全体のテーブルを作ったりすると、その外側の型はひとつ上の宇宙に上がります。 -/
