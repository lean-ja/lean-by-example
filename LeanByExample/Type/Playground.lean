/- # subsingleton elimination の例を作りたい -/

/- ## TPiL から引用

この最後の規則には例外があります。それは、**帰納的に定義された `Prop` から任意の `Sort` への elimination が許される場合**です。条件は、**コンストラクタが1つだけであり、その各引数が `Prop` かインデックスであること**です。

このときの直感としては、「その型の引数が inhabited（居住可能）であるという事実だけで、情報の利用が完結しており、新たなデータの構成を伴わない」という点にあります。この特別なケースは **singleton elimination（単一要素消去）** として知られています。

私たちはすでにこの singleton elimination を、**等式型の eliminator である `Eq.rec` の応用で見てきました**。たとえば `h : Eq a b` を使って、`t' : p a` を `p b` にキャストできます。このとき `p a` と `p b` は任意の型であっても構いません。なぜならこのキャストは**新しいデータを生成するのではなく、既存のデータを別の形で解釈し直しているだけ**だからです。

singleton elimination はまた、**異種等式（heterogeneous equality）** や **well-founded 再帰** の文脈でも使われます。これらについては後の「帰納法と再帰」の章で説明されます。
-/

variable (p : Type → Type)

-- 証明項 `h : α = β` からデータ `p α → p β` を生成する関数
def castFunc {α β : Type} (h : α = β) : p α → p β := fun x =>
  match h with
  | rfl => x
