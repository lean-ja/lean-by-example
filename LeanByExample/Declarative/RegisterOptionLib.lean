-- RegisrerOptionLib.lean の内容
import Lean

open Lean

register_option greeting : String := {
  defValue := "Hello World"
  descr := "just a friendly greeting"
}
