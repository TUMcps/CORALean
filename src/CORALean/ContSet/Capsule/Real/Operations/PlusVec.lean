import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.plusVec`

CORA's `@capsule/plus.m` with a vector: a capsule plus a vector is a capsule, the centre shifted,
generator and radius unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Capsule plus vector: the centre shifted, generator and radius unchanged. -/
def Capsule.plusVec (C : Capsule n) (v : Vec ℝ n) : Capsule n := ⟨C.c + v, C.g, C.r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
