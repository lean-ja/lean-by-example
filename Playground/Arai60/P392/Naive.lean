/-
2つの文字列 `s` と `t` が与えられたとき、`s` が `t` の部分列であれば `true` を、そうでなければ `false` を返してください。

文字列の部分列とは、元の文字列からいくつかの文字（0個でもよい）を削除して、残った文字の相対的な順序を変えずに作られる新しい文字列のことです。（例："ace" は "abcde" の部分列ですが、"aec" は違います）

-/

-- **TODO** List.isSublist を自前で実装するのは良い演習問題になりそう
def String.isSubsequence (needle haystack : String) : Bool :=
  List.isSublist needle.toList haystack.toList

#guard String.isSubsequence "abc" "ahbgdc" -- true
#guard ! String.isSubsequence "axc" "ahbgdc" -- false
#guard String.isSubsequence "" "ahbgdc" -- true
