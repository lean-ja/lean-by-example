import Playground.MyList.Basic

namespace MyList

open Lean PrettyPrinter

#check Unexpander

@[app_unexpander MyList.cons]
def cons.unexpander : Unexpander := fun stx =>
  match stx with
  | `(MyList.cons $head $tail) => `(m[$head, $tail])
  | _ => throw ()

-- **TODO**: 上手くいかない
#check MyList.cons 1 (MyList.cons 2 (MyList.cons 3 MyList.nil))

#check m[1, 2, 3]

end MyList
