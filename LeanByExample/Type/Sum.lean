/- # Sum

`Sum` は、データの選択肢を束ねたものを表現しており、`Sum A B` は `A` と `B` のどちらかの値を取るような型です。`A ⊕ B` と表記されます。
-/

#check (Sum.inl 42 : Nat ⊕ String)
#check (Sum.inr "hello world" : Nat ⊕ String)
