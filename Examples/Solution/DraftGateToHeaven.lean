import Mathlib.Tactic.ITauto

--#--
section
/- ## 選択原理を使用していないことを確認するコマンド -/

open Lean Elab Command

elab "#detect_classical " id:ident : command => do
  -- 識別子(ident)を Name に変換
  let constName ← liftCoreM <| realizeGlobalConstNoOverload id

  -- 依存する公理を取得
  let axioms ← collectAxioms constName

  -- 依存公理がなかったときの処理
  if axioms.isEmpty then
    logInfo m!"'{constName}' does not depend on any axioms"
    return ()

  -- Classical で始まる公理があるかどうかチェック
  -- もしあればエラーにする
  let caxes := axioms.filter fun nm => Name.isPrefixOf `Classical nm
  if caxes.isEmpty then
    logInfo m!"'{constName}' is non-classical and depends on axioms: {axioms.toList}"
  else
    throwError m!"'{constName}' depends on classical axioms: {caxes.toList}"

end
--#--



/-- 門番。左の門番と右の門番の2人 -/
inductive Gatekeeper : Type where
  /-- 左の門番 -/
  | left
  /-- 右の門番 -/
  | right
deriving DecidableEq

/-- 門 -/
inductive Gate : Type where
  /-- 天国への門 -/
  | heaven
  /-- 地獄への門 -/
  | hell
deriving DecidableEq

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
  itauto

/-- 悪魔でないことは天使であることと同値 -/
@[simp] theorem of_not_devil {g : Gatekeeper} : ¬ g.devil ↔ g.angel := by
  have or := angel_or_devil g
  have ne := angel_ne_devil g
  itauto

#detect_classical of_not_angel
#detect_classical of_not_devil




-- 知識の表現と、天使や悪魔への質問の表現
section

abbrev Known (p : Prop) := Decidable p

/-- 門番は、真偽を知っている質問には答えてくれる -/
opaque answer (g : Gatekeeper) (question : Prop) [Known question] : Bool

variable {g : Gatekeeper} {question : Prop} [Known question]

/-- 知られていることに対して、天使が「はい」と答えることと真であることは同値。 -/
@[simp] axiom angel_yes (ha : angel g) : g.answer question = true ↔ question

/-- 知られていることに対して、悪魔が「はい」と答えることと偽であることは同値。 -/
@[simp] axiom devil_yes (hd : devil g) : g.answer question = true ↔ ¬ question

/-- 知られていることに対して、天使が「いいえ」と答えることと偽であることは同値。 -/
@[simp] axiom angel_no (ha : angel g) : g.answer question = false ↔ ¬ question

/-- 知られていることに対して、悪魔が「いいえ」と答えることと真であることは同値。
排中律を仮定しないため、公理として仮定している。 -/
@[simp] axiom devil_no (hd : devil g) : g.answer question = false ↔ question

#detect_classical angel_no
#detect_classical devil_no

end



-- 知識に関する仮定

-- 門番たちはお互いが天使か悪魔か知っている
@[instance] axiom instKnownAngel (g : Gatekeeper) : Known (angel g)

@[instance] axiom instKnownDevil (g : Gatekeeper) : Known (devil g)



-- 門番たちは、それぞれの門に対して、その門が天国か地獄かを知っている
instance (gate : Gate) : Known (gate = Gate.heaven) := by exact decEq gate Gate.heaven



-- 簡単な質問に対する答えを証明する
section

/-- 「あなたは悪魔ですか」とどちらの門番に訊いても、必ず「いいえ」と答える -/
theorem both_says_no_asked_if_devil (g : Gatekeeper) : g.answer (devil g) = false := by
  -- g が天使であるか悪魔であるかで場合分けをする
  cases angel_or_devil g

  -- g が天使のとき
  case inl h =>
    -- 天使なので「いいえ」と答える
    simpa [angel_no h]

  -- g が悪魔のとき
  case inr h =>
    -- 実際に悪魔なので本音は「はい」だが
    -- 悪魔なので嘘をついて「いいえ」と答える
    simpa [devil_no h]

end

def correct_question (g : Gatekeeper) (gate : Gate) : Prop := -- sorry
   g.answer (gate = .heaven) = true

-- この公理は選択原理よりは弱いのでまあ問題ないだろう
@[instance] axiom instKnownCorrectQuestion (g : Gatekeeper) (gate : Gate) : Known (correct_question g gate)

/-- 「この門は天国への門ですか？」と訊いたらあなたはYESと答えますか？と質問すればよい。-/
theorem gate_to_heaven (g : Gatekeeper) (gate : Gate) : (g.answer (correct_question g gate) ↔ gate = .heaven) := by
  dsimp [correct_question]
  constructor <;> intro h

  case mpr =>
    rcases angel_or_devil g with hor | hor
    · simpa [angel_yes hor]
    · simpa [devil_yes hor]

  case mp =>
    rcases angel_or_devil g with hor | hor
    · simpa [angel_yes hor] using h
    · simpa [devil_yes hor] using h

-- ところで、なぜ選択原理への依存をチェックしているのだろう？
-- この問題は選択原理を使用すると何がまずいのだろうか。
-- 選択原理を許してもいいのでは？？？
#detect_classical gate_to_heaven

end Gatekeeper
