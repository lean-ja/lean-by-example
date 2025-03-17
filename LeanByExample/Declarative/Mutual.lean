/- # mutual

`mutual` は、相互再帰を定義するために使用されます。

以下は、作為的ではあるものの簡単な例です。
-/
mutual

  /-- 偶数 -/
  def even (n : Nat) : Bool :=
    match n with
    | 0 => true
    | n + 1 => odd n

  /-- 奇数 -/
  def odd (n : Nat) : Bool :=
    match n with
    | 0 => false
    | n + 1 => even n

end

#guard even 4

#guard odd 5
