/-- 門番。左の門番と右の門番の2人 -/
inductive Gatekeeper : Type where
  /-- 左の門番 -/
  | left
  /-- 右の門番 -/
  | right

namespace Gatekeeper

/-- 天使であることを表す述語 -/
opaque angel (g : Gatekeeper) : Prop

/-- 悪魔であることを表す述語 -/
opaque devil (g : Gatekeeper) : Prop

/-- 門番は天使であるか悪魔であるかのどちらか -/
axiom angel_or_devil (g : Gatekeeper) : angel g ∨ devil g

/-- 門番が天使かつ悪魔であることはない -/
axiom angel_ne_devil (g : Gatekeeper) : ¬(angel g ∧ devil g)

/-- 天使でないことは悪魔であることと同値 -/
@[simp] theorem of_not_angel {g : Gatekeeper} : ¬ g.angel ↔ g.devil := by
  have or := angel_or_devil g
  have ne := angel_ne_devil g
  constructor
  all_goals
    intro h
    simp_all

/-- 悪魔でないことは天使であることと同値 -/
@[simp] theorem of_not_devil {g : Gatekeeper} : ¬ g.devil ↔ g.angel := by
  simp [← of_not_angel]

/-- 仮定の中に `angel g` と `devil g` があったときに矛盾を導くという
機能を追加した`contradiction` -/
macro "contradiction!" : tactic => `(tactic| with_reducible
    try contradiction
    try simp_all only [
      ← of_not_angel,
      not_true_eq_false,
      not_false_eq_true
    ]
  )

/- 門番に対して、質問をすることができる。門番はそれに対して「はい」か「いいえ」で答えてくれる。
「はい」か「いいえ」で答えられない質問はできない。 -/
opaque answer (g : Gatekeeper) (question : Prop) : Bool

/-- 天使が「はい」と答えることは真であることと同値 -/
axiom angel_says_true {g : Gatekeeper} {question : Prop} (h : angel g) : g.answer question = true ↔ question

/-- 悪魔が「はい」と答えることは偽であると同値 -/
axiom devil_says_true {g: Gatekeeper} {question : Prop} (h : devil g) : g.answer question = true ↔ ¬ question

/-- 天使が「いいえ」と答えることは偽であることと同値 -/
@[simp] theorem angel_says_false {g : Gatekeeper} {question : Prop} (h : angel g) :
    g.answer question = false ↔ ¬ question := by
  -- 同値の両方向を示す
  constructor <;> intro h

  all_goals
    -- g は天使なので正直。よって明らか
    have := angel_says_true (question := question) (show g.angel by assumption)
    simp_all

/-- 悪魔が「いいえ」と答えることは真であることと同値 -/
@[simp] theorem devil_says_false {g : Gatekeeper} {question : Prop} (h : devil g) :
    g.answer question = false ↔ question := by
  -- 同値の両方向を示す
  constructor <;> intro h

  all_goals
    -- g は悪魔なので嘘つき。よって明らか
    have := devil_says_true (question := question) (show g.devil by assumption)
    simp_all

/-- 「あなたは悪魔ですか」とどちらの門番に訊いても、必ず「いいえ」と答える -/
theorem both_says_false_asked_if_devil (g : Gatekeeper) : g.answer (devil g) = false := by
  -- g が天使であるか悪魔であるかで場合分けをする
  cases angel_or_devil g

  -- g が天使のとき
  case inl h =>
    -- 天使なので「いいえ」と答える
    simpa [angel_says_false h]

  -- g が悪魔のとき
  case inr h =>
    -- 実際に悪魔なので本音は「はい」だが
    -- 悪魔なので嘘をついて「いいえ」と答える
    simpa [devil_says_false h]

-- /-- 「もう一人の門番」を表す関数 -/
-- def another (g : Gatekeeper) : Gatekeeper :=
--   match g with
--   | left => right
--   | right => left

-- /-- 門番は２人しかいないので、g, g' が門番なら
-- `g' = g` または `g' = g.another` -/
-- theorem or_another (g g' : Gatekeeper) : g = g' ∨ g' = g.another := by
--   -- g, g' が左右どちらの門番かで場合分けをする
--   cases g <;> cases g'

--   -- 計算すれば正しいことがわかる
--   all_goals simp_all [another]

/-- 門番が２人いるときに「もう一人の門番は悪魔ですか？」と訊くと、
二人の門番がともに天使またはともに悪魔であるかどうかが分かる。 -/
theorem detect_same (g g' : Gatekeeper) :
    g.answer (devil g') = false ↔ (g.angel ∧ g'.angel ∨ g.devil ∧ g'.devil) := by
  -- 同値の両方向を示す
  constructor <;> intro h

  -- 右から左を示す
  case mpr =>
    -- ともに天使であるか、ともに悪魔であるかで場合分けをする
    rcases h with ⟨ha, ha'⟩ | ⟨hd, hd'⟩

    -- ともに天使であるとき
    case inl =>
      -- 天使なので正直に「いいえ」と答える
      simpa [angel_says_false ha]

    -- ともに悪魔であるとき
    case inr =>
      -- 悪魔なので嘘をついて「いいえ」と答える
      simpa [devil_says_false hd]

  -- 左から右を示す
  case mp =>
    -- g は天使であるか悪魔であるかのどちらか
    -- どちらであるかに応じて場合分けをする
    rcases angel_or_devil g with ha | hd

    -- g が天使のとき
    case inl =>
      -- 天使が「いいえ」と答えているから悪魔ではない
      simp [angel_says_false ha] at h
      simp_all

    -- g が悪魔のとき
    case inr =>
      -- 悪魔が「いいえ」と答えているから悪魔である
      simp [devil_says_false hd] at h
      simp_all

end Gatekeeper
