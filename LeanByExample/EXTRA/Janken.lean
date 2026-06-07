/- # じゃんけんゲーム

じゃんけんゲームを CLI で実装する例を紹介します。以下のような仕様で実装しましょう。

* ユーザはテキストで「グー」「チョキ」「パー」のいずれかを入力する。
* コンピュータはランダムに手を選ぶ（後出ししているように見えるが、実際にはランダム）
* あいこだった場合は勝負がつくまで何度でも繰り返す。

## ステップ1: ユーザが入力した手を表示する

Lean でプログラムを書く際はだいたいいつもそうですが、必要なデータ型を定義するところから始めます。じゃんけんの手を表す型 `Hand` を定義しましょう。グー・チョキ・パーの３種類です。
-/

/-- じゃんけんの手 -/
inductive Hand where
  /-- グー -/
  | gu
  /-- チョキ -/
  | choki
  /-- パー -/
  | pa
deriving BEq, Inhabited

protected def Hand.toString : Hand → String
  | .gu => "グー"
  | .choki => "チョキ"
  | .pa => "パー"

instance : ToString Hand where
  toString := Hand.toString

/-
次に、ユーザから受け取る文字列をパースして `Hand` に変換する関数を用意しましょう。文字列のパースに成功するとは限りませんが、その場合は成功するまで繰り返し何度でも入力を促すことにします。
-/

/-- ユーザからの入力を受け取る -/
def getUserInput : IO String := do
  -- 入力待ちを表す記号を表示
  IO.print "> "

  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let result := input.trimAscii.copy
  return result

/-- 文字列を読んで Hand に変換する -/
def parseHand (input : String) : Option Hand :=
  match input with
  | "グー" => some Hand.gu
  | "チョキ" => some Hand.choki
  | "パー" => some Hand.pa
  | _ => none

/-- ユーザからの入力を受け取ってパース済みの値を返す。
パースに失敗した場合は、成功するまで繰り返す -/
partial def getUserHand : IO Hand := do
  let userInput ← getUserInput
  let some hand := parseHand userInput |
    IO.println "そんな手はないよ！もう一回！"
    getUserHand
  return hand

/-
ここまで終わったら、いったんここまでのコードを使って `main` 関数を実装してみます。

{{#include ./Janken/Step1.md}}
-/

/-
この段階でもしうまく行かなければ、日本語の文字が文字化けしている可能性があります。[インストール方法](#{root}/HowToInstall.md)のターミナルでの文字化けの修正方法を試してみてください。
-/

/- ## ステップ2: コンピュータとの勝負を実装する

次にやるべきことは、コンピュータの手をランダムに選ぶことです。Lean には乱数を生成するための関数が用意されているので、それを使います。
-/

/-- ランダムに手を選ぶ -/
def getRandomHand : IO Hand := do
  let n ← IO.rand 1 3
  let hand :=
    match n with
    | 1 => Hand.gu
    | 2 => Hand.choki
    | 3 => Hand.pa
    | _ => unreachable!
  return hand

-- ちゃんと３つの手が全部出るか確認する
#eval List.range 10 |>.mapM (fun _ => getRandomHand)

/- 問題がなければ、勝敗判定を実装します。 -/

/-- h1 が h2 に勝つかどうかを判定する -/
def Hand.beat (h1 h2 : Hand) : Bool :=
  match h1, h2 with
  | .gu, .choki => true
  | .choki, .pa => true
  | .pa, .gu => true
  | _, _ => false

/-
ここまで終われば、最後まで実装することができるでしょう。
あいこだった場合は、勝負がつくまで何度でも繰り返すことにします。
-/

/-
{{#include ./Janken/Step2.md}}
-/
