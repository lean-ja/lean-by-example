---
name: style-check
description: .lean ファイルを編集・追加するときにコードの書き方をチェックするために使う。
---

# Lean コードスタイルチェック

## パターンマッチする変数に名前を付ける

コードを書くときには、以下のようなパターンマッチする変数に名前をつけないスタイルは使用しないようにする。

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n
```

次のように、パターンマッチする変数に名前を付けるスタイルで書くこと。

```lean
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
```

## where は省略しない

`inductive` コマンドや `structure` コマンドの `where` は省略しないで書くこと。

## do 構文を適切に使う

関数の実装について、`do` 構文を使って命令的に書いた方がわかりやすくなる場合は、`do` 構文を使って書くこと。
