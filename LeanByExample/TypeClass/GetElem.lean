/- # GetElem
`GetElem` 型クラスは、リストや配列などの「データの直線的な集まり」を表す型 `Col` の項 `as : Col` に対して、その `i` 番目の要素を取得する方法を提供します。`GetElem` 型クラスを実装すると、`as[i]` というインデックスアクセスの構文が使用できるようになります。
-/

/-- 標準にある List を真似て作ったデータ構造 -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α

private def Three := MyList.cons 1 (MyList.cons 2 (MyList.cons 3 MyList.nil))

-- 作ったばかりで実装していないため、
-- インデックスアクセスの構文 `as[i]` が使えない
#guard_msgs (drop warning) in --#
#check_failure Three[2]

variable {α : Type}

/-- リストの長さを返す関数 -/
def MyList.length {α : Type} (l : MyList α) : Nat :=
  match l with
  | nil => 0
  | cons _ t => 1 + length t

/-- `as : MyList` の `idx` 番目の要素を取得する。
`idx` の型は `Fin` としてある。 -/
def MyList.get (as : MyList α) (idx : Fin as.length) : α :=
  match as, idx with
  | .cons head _, ⟨0, _⟩ => head
  | .cons _ as, ⟨i + 1, h⟩ => by
    -- インデックスアクセスが範囲内であることを証明する
    have bound : i < as.length := by
      simp [MyList.length] at h
      omega
    exact MyList.get as ⟨i, bound⟩

/-- MyList を GetElem のインスタンスにする -/
instance : GetElem (MyList α) Nat α (fun as i => i < as.length) where
  getElem as i h := as.get ⟨i, h⟩

-- インデックスアクセスの構文が使えるようになった
#guard Three[2] = 3

/- ## インデックスアクセスの種類
コレクション `as` に対して、`i` 番目の要素を取得すると書きましたが、`i` 番目の要素があるとは限らないという問題があります。これに対処するには様々な方法がありえますが、中でも以下のものは専用の構文が用意されています。

* `as[i]`: インデックス `i` が範囲内であることの証明を自動で構成する。`i` が変数になっていて具体的に計算できないときでも、ローカルコンテキスト内に `i` が範囲内であることの証明があれば動作する。
* `as[i]?`: 返り値を [`Option`](#{root}/Type/Option.md) に包む。範囲外の場合は `none` を返す
* `xs[i]!`: `i` が範囲外だった時には `panic` する。
* `xs[i]'h`: `i` が範囲内であることの証明 `h` を渡す。
-/

-- 具体的な数値を渡せば、それが範囲内であることを自動的に証明してくれる
#guard [1, 2, 3][2] = 3

#eval show IO Unit from do
  let l : List Nat := [1, 2, 3]
  -- for 文を回すときに `h : i` とすると
  -- `i` についての情報を取得できる
  for h : i in [0:3] do
    -- インデックスが範囲内であることを証明する
    have : i < l.length := Membership.get_elem_helper h rfl

    IO.println l[i]

-- 返り値を Option に包む場合
#guard Three[2]? = some 3
#guard Three[3]? = none

-- 範囲外なら panic することにして強引に値を取り出す
#guard Three[2]! = 3

-- インデックスが範囲内であることの証明を明示的に渡す
#guard
  let h := show 2 < Three.length from by decide
  Three[2]'h = 3
