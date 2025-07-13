-- 集合Sとその上の二項関係Rを考えたい
variable {S : Type} (R : S → S → Prop)

local infix:50 "∼R" => R

/-- 二項関係が反射的 -/
def Reflexive := ∀ x, x ∼R x

/-- 二項関係が対称的 -/
def Symmetric := ∀ x y, x ∼R y → y ∼R x

/-- 二項関係が推移的 -/
def Transitive := ∀ x y z, x ∼R y → y ∼R z → x ∼R z

/-- 二項関係が反対称的 -/
def Antisymmetric := ∀ x y, x ∼R y → y ∼R x → x = y
