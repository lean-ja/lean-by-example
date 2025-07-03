import Playground.MyList.Basic

namespace MyList

open Lean PrettyPrinter

@[app_unexpander MyList.nil]
def unexpandMyListNil : Unexpander := fun stx =>
  match stx with
  | `($(_)) => `(m[])

@[app_unexpander MyList.cons]
def cons.unexpander : Unexpander := fun stx =>
  match stx with
  | `($(_) $head $tail) =>
    match tail with
    | `(m[]) => `(m[ $head ])
    | `(m[ $xs,* ]) => `(m[ $head, $xs,* ])
    | `(⋯) => `(m[ $head, $tail ])
    | _ => throw ()
  | _ => throw ()

#check (m[] : MyList Nat)
#check m[1, 2, 3]

end MyList
