/- # 生文字列リテラル

文字列リテラルはダブルクォート `#` で囲って表現しますが、では `"` を含む文字列を書きたいときはどうすれば良いのでしょうか？エスケープシークエンスを付けて「これは文字列リテラルの開始/終了の意味ではないよ」と示すのが良くある方法ですね。
-/

/-- info: I said "Hello" to you. -/
#guard_msgs in --#
#eval IO.println "I said \"Hello\" to you."

/-
それが面倒あるいは困難であるとき、`r#"` と `"#` で囲むという構文が使用できます。これは **生文字列リテラル(raw string literal)** と呼ばれるものです。
-/

def json := r#"
  {
    "name": "Alice",
    "age": 30,
    "isStudent": false
  }
"#

/--
info:
  {
    "name": "Alice",
    "age": 30,
    "isStudent": false
  }
-/
#guard_msgs in --#
#eval IO.println json
