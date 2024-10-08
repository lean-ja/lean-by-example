/- # relaxedAutoImplicit

`relaxedAutoImplicit` オプションは、[`autoImplicit`](./AutoImplicit.md) オプションの派生オプションであり、自動束縛の対象を広げます。
-/
import Lean --#
-- `autoImplicit` は有効にしておく
set_option autoImplicit true

section
  -- `relaxedAutoImplicit` が無効の時
  set_option relaxedAutoImplicit false

  -- 二文字の識別子は自動束縛の対象にならないのでエラーになる
  /-- error: unknown identifier 'AB' -/
  #guard_msgs in
    def nonempty₁ : List AB → Bool
      | [] => false
      | _ :: _ => true
end

section
  -- `relaxedAutoImplicit` が有効の時
  set_option relaxedAutoImplicit true

  -- 二文字の識別子も自動束縛の対象になるのでエラーになる
  def nonempty₂ : List AB → Bool
    | [] => false
    | _ :: _ => true
end

/- ## 問題点

```admonish error title="非推奨"
この機能には以下の問題点が指摘されており使用は推奨されません。
* タイポを見過ごしやすくなってしまう
* 自動束縛の結果どのような型になるか指定できないため、意図しない型に束縛されてバグを引き起こす可能性がある
```

デフォルトではこのオプションは有効になっているため、`lakefile` の設定で無効にすることをお勧めします。
-/

open Lean Elab Command

/-- オプションのデフォルト値を取得する関数 -/
def getDefaultValue (opt : Name) : CommandElabM Unit := do
  let decls ← getOptionDecls
  match decls.find? opt with
  | some decl =>
    logInfo m!"default value of {opt} is {decl.defValue}"
  | none =>
    logInfo m!"{opt} is unknown"

/-- info: default value of relaxedAutoImplicit is true -/
#guard_msgs in
  #eval getDefaultValue `relaxedAutoImplicit
