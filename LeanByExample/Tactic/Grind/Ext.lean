
/-- 2次元の点を表す構造体 -/
@[ext]
structure Point where
  x : Int
  y : Int

/- `Point` の外延性定理 `Point.ext` を `grind` に登録するには、
構造体名に `attribute [grind ext]` を付与します。 -/
attribute [grind ext] Point

/- これで `grind` が `Point` の等式をフィールドごとの等式に分解できるようになります。 -/
example (p : Point) (a : Int) :
    a = p.x → p = ⟨a, p.y⟩ := by
  grind

/- 関数外延性 (`funext`) は標準ライブラリで `@[grind ext]` 相当として登録されているため、
関数等式も `grind` で扱うことができます。 -/
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  grind

/- `grind -ext` と指定すると、外延性推論を無効化することができます。
外延性を無効化すると、上記のような関数等式の証明が失敗します。 -/
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  fail_if_success grind -ext
  grind

/- `grind +extAll` と指定すると、環境内のすべての `@[ext]` 定理を外延性推論に使います。
`@[grind ext]` が付いていなくても `@[ext]` が付いていれば使用されます。 -/
example (p : Point) (a : Int) :
    a = p.x → p = ⟨a, p.y⟩ := by
  grind +extAll

/- 構造体名ではなく、外延性定理そのものに `@[grind ext]` を付けることもできます。 -/

/-- 値を一つ持つラッパー型 -/
structure Box where
  val : Nat

@[ext]
@[grind ext]
theorem Box.ext {a b : Box} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

example (a b : Box) (h : a.val = b.val) : a = b := by
  grind
