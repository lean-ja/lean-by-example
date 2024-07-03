/- # opaque -/

opaque A : Type
opaque B : Type
opaque C : Type

variable [Inhabited C]

opaque f : (A → B) → C

#check_failure f f
