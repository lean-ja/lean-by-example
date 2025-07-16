def x : Fin (4 + 2) := Fin.mk 5 sorry

#check x

#check cast (by conv => simp) x
