/- # trivial

`trivial` は明らかな(trivial)ことを示します。-/

-- True は何の仮定もなしに示せる
example : True := by trivial

-- 定義から明らかな等式
example : 1 + 1 = 2 := by trivial

-- 矛盾があるので, どんな命題でも証明できる
example (P : Prop) (h : False) : P := by trivial

/- ## 舞台裏
`trivial` は、複数のタクティクを順に試すマクロとして実装されています。`trace.Elab.step` というオプションを `true` にすると、展開の様子を順を追って見ることができます.-/

/--
info: [Elab.step] trivial
  [Elab.step] trivial
    [Elab.step] trivial
      [Elab.step] (apply And.intro✝) <;> trivial
        [Elab.step] focus
              apply And.intro✝
              with_annotate_state"<;>" skip
              all_goals trivial
          [Elab.step] ⏎
                apply And.intro✝
                with_annotate_state"<;>" skip
                all_goals trivial
            [Elab.step] ⏎
                  apply And.intro✝
                  with_annotate_state"<;>" skip
                  all_goals trivial
              [Elab.step] apply And.intro✝
      [Elab.step] apply True.intro✝
      [Elab.step] decide
      [Elab.step] contradiction
-/
#guard_msgs in
example (P : Prop) (h : False) : P := by
  set_option trace.Elab.step true in
  trivial

/- 出力が長いのですが、まず `apply And.intro` を試し、次に `apply True.intro` を試し、次に [`decide`](./Decide.md) と [`contradiction`](./Contradiction.md) を試していることがわかります。 -/
