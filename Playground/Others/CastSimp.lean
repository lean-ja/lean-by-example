def x : Fin (4 + 2) := Fin.mk 5 (by omega)

#check x

#check cast (by conv => simp) x
