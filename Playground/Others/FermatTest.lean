def fermatTest (n : Nat) : Bool := Id.run do
  let candidates := List.range n
  for a in candidates do
    if Nat.gcd a n != 1 then
      continue
    -- **TODO** 剰余を毎回とりながら計算すべき。それにはどうしたらいい？
    -- また、`a ^ (n - 1)` の計算には繰り返し二乗法を使うべきだ。
    if (a ^ (n - 1)) % n != 1 then
      return false
  true

#eval fermatTest 23
