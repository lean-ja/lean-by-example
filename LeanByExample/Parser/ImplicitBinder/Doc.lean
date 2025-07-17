/-
> Implicit binder, like `{x y : A}` or `{x y}`.
> In regular applications, whenever all parameters before it have been specified,
> then a `_` placeholder is automatically inserted for this parameter.
> Implicit parameters should be able to be determined from the other arguments and the return type
> by unification.
>
> In `@` explicit mode, implicit binders behave like explicit binders.
-/
--#--
import LeanByExample.DocCmd
/--
info: Implicit binder, like `{x y : A}` or `{x y}`.
In regular applications, whenever all parameters before it have been specified,
then a `_` placeholder is automatically inserted for this parameter.
Implicit parameters should be able to be determined from the other arguments and the return type
by unification.

In `@` explicit mode, implicit binders behave like explicit binders.
-/
#guard_msgs in
#doc Lean.Parser.Term.implicitBinder
--#--
