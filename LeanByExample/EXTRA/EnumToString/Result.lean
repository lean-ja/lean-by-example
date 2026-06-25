import LeanByExample.EXTRA.EnumToString.Register --#

inductive Hoge where
  | a
  | b
  | c
deriving ToString

#guard toString Hoge.a = "a"
#guard toString Hoge.c = "c"
