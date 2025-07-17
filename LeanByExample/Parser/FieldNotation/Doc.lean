/-
> The *extended field notation* `e.f` is roughly short for `T.f e` where `T` is the type of `e`.
> More precisely,
> * if `e` is of a function type, `e.f` is translated to `Function.f (p := e)`
>   where `p` is the first explicit parameter of function type
> * if `e` is of a named type `T ...` and there is a declaration `T.f` (possibly from `export`),
>   `e.f` is translated to `T.f (p := e)` where `p` is the first explicit parameter of type `T ...`
> * otherwise, if `e` is of a structure type,
>   the above is repeated for every base type of the structure.
>
> The field index notation `e.i`, where `i` is a positive number,
> is short for accessing the `i`-th field (1-indexed) of `e` if it is of a structure type.
-/
--#--
import LeanByExample.DocCmd
/--
info: The *extended field notation* `e.f` is roughly short for `T.f e` where `T` is the type of `e`.
More precisely,
* if `e` is of a function type, `e.f` is translated to `Function.f (p := e)`
  where `p` is the first explicit parameter of function type
* if `e` is of a named type `T ...` and there is a declaration `T.f` (possibly from `export`),
  `e.f` is translated to `T.f (p := e)` where `p` is the first explicit parameter of type `T ...`
* otherwise, if `e` is of a structure type,
  the above is repeated for every base type of the structure.

The field index notation `e.i`, where `i` is a positive number,
is short for accessing the `i`-th field (1-indexed) of `e` if it is of a structure type.
-/
#guard_msgs in
#doc Lean.Parser.Term.proj
--#--
