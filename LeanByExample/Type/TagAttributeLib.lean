-- TagAttributeLib.lean の内容
import Lean

open Lean

initialize myTagAttribute : TagAttribute ←
  registerTagAttribute (name := `my_tag) (descr := "タグ属性のテスト")
