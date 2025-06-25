-- TagAttributeLib.lean の内容
import Lean

open Lean

initialize myTagAttribute : TagAttribute ←
  registerTagAttribute `my_tag "タグ属性のテスト"
