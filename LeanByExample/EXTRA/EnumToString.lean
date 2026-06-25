/- # 列挙型に対する `ToString` インスタンスの自動生成

## やりたいことの説明

帰納型であって、すべてのコンストラクタが一切引数を持たないものを、**列挙型(enumeration type)** と呼びます。
たとえば、以下に示すのは列挙型になっている例です。
-/

/-- 色 -/
inductive Color where
  | red
  | green
  | blue

/-
おおまかに、「有限個の候補からどれか一つを選ぶ」という情報だけを持っているのが列挙型であると言えます。

さて、列挙型に対して `ToString` インスタンスを定義する場合、各コンストラクタに対応する文字列を返したい場合が多いでしょう。
上記の例であれば、次のように定義するわけです。
-/

protected def Color.toString (c : Color) : String :=
  match c with
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

instance : ToString Color where
  toString := Color.toString

/-
これは決まりきったルーチンワークなので、「自動化したい」という欲求が湧いてきます。
自動化するにはどうすればいいでしょうか？
-/

/- ## 列挙型であるか判定する

方針としては、列挙型に対してだけ動作する、`ToString` の deriving handler を定義したいです。
`deriving instance ToString for Color` のように書いたら、`Color` の `ToString` インスタンスが自動生成されるようにしたいわけです。
現状では実装していないので、当然失敗します。
これが成功するようにしましょう。
-/

/-- error: No deriving handlers have been implemented for class `ToString` -/
#guard_msgs in --#
deriving instance ToString for Color


/-
deriving handler が内部で何をするかというと、実は手動で定義するときと同じことを自動でやっているだけです。
以下がおおまかな流れです。

1. まず列挙型かどうか判定して、列挙型でなければ即終了
2. 列挙型だったら `instance` コマンドを生成する
3. 生成したコマンドを実行して、インスタンスを作る

したがってまずやるべきことは、列挙型かどうか判定することです。

これには専用の関数が用意されており、`Lean.isEnumType` という関数で判定することができます。

{{#include ./EnumToString/IsEnumType.md}}
-/

/- ## `instance` コマンドを自動生成する

{{#include ./EnumToString/MkToStringInst.md}}
-/


/- ## deriving handler を宣言する

ここまで終わったら、後は deriving handler を宣言するだけです。
`initialize` コマンドで登録することができます。

{{#include ./EnumToString/Register.md}}
-/

/-
これで、晴れて `deriving ToString` が列挙型に対して使えるようになりました。
`initialize` コマンドの効果はモジュール（ファイルのこと）を跨がないと発生しないのですが、ファイルを跨げばこういう感じで書けるようになっているはずです。

{{#include ./EnumToString/Result.md}}
-/
