/- # export

`export` コマンドは、他の名前空間から定義を現在の名前空間に追加します。

具体的には、`Some.Namespace` の配下に `nameᵢ` がある状態で `export Some.Namespace (name₁ name₂ ...)` を実行することにより、以下の両方の処理が行われます。

* [`open`](./Open.md) と同様に、`nameᵢ` が `Some.Namespace` の接頭辞なしで現在の名前空間 `N` 上で見えるようになります。
* 現在の名前空間 `N` の外部の名前空間から `N.nameᵢ` としてアクセスできるようになります。
-/
namespace N -- export コマンドが実行される名前空間

  inductive Sample : Type where
    | foo
    | bar
    | baz

  -- foo は名前空間 Sample 上にあるので、
  -- 短い名前ではアクセスできない
  #check_failure foo
  #check Sample.foo

  -- foo を現在の名前空間 N に追加する
  export N.Sample (foo)

  -- 短い名前でもアクセス可能になった
  #check foo

end N

-- 名前空間 `N` の外部からアクセスするには、
-- 普通はフルネームが必要
#check_failure N.bar
#check N.Sample.bar

-- しかし foo は名前空間 N の内部で export されているので、
-- N を指定するだけでアクセス可能
#check N.foo
