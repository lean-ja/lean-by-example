/-
> A string is a sequence of Unicode code points.
>
> At runtime, strings are represented by [dynamic arrays](https://en.wikipedia.org/wiki/Dynamic_array)
> of bytes using the UTF-8 encoding. Both the size in bytes (`String.utf8ByteSize`) and in characters
> (`String.length`) are cached and take constant time. Many operations on strings perform in-place
> modifications when the reference to the string is unique.
-/
--#--
import LeanByExample.DocCmd

/--
info: A string is a sequence of Unicode code points.

At runtime, strings are represented by [dynamic arrays](https://en.wikipedia.org/wiki/Dynamic_array)
of bytes using the UTF-8 encoding. Both the size in bytes (`String.utf8ByteSize`) and in characters
(`String.length`) are cached and take constant time. Many operations on strings perform in-place
modifications when the reference to the string is unique.
-/
#guard_msgs in
#doc String
--#--
