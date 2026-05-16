/- `Lean.Parser.Term.strictImplicitBinder` のドキュメント表示用ファイル -/
--#--
import LeanByExample.DocCmd
/--
info: Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`.
In contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert
a `_` placeholder until at least one subsequent explicit parameter is specified.
Do *not* use strict-implicit binders unless there is a subsequent explicit parameter.
Assuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.

Example: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,
then `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,
and `h hs` has type `p y`.
In contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h'` by itself elaborates to have type `?m ∈ s → p ?m`
with `?m` a fresh metavariable.
-/
#guard_msgs in
#doc Lean.Parser.Term.strictImplicitBinder
--#--
