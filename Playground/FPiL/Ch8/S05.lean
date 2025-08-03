-- `Fin` でラップしてもポインタアドレスが変わらないので、
-- 実行時のオーバーヘッドがないことがわかる
unsafe def main : IO Unit := do
  let x := 5
  let finite : Fin 10 := ⟨x, by omega⟩
  IO.println (ptrAddrUnsafe x)
  IO.println (ptrAddrUnsafe finite)

#eval main
#eval (5 : Fin 8)

variable {α : Type}

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none

-- 返り値が`Fin`に包まれていることに注目
-- インデックスを、正当性証明付きで返すことができる
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0

-- 昔は Fin n を引数に取っていたけど、アップデートで取らなくなった
#check Array.get

/- ## Exercise -/

def Fin.next? {n : Nat} (x : Fin n) : Option (Fin n) :=
  if h : x.val + 1 < n then
    some ⟨x.val + 1, h⟩
  else none

#guard (3 : Fin 8).next? = some 4
#guard (7 : Fin 8).next? = none
