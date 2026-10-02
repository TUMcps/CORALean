import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.project`

CORA's `@capsule/project.m`: centre and generator at the chosen coordinates, the radius unchanged,
`C.c(dims)`, `C.g(dims)`, `C.r`. `Capsule.reindex` is the case where `dims` is a permutation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Centre and generator read at `dims`, the radius unchanged. -/
def Capsule.project (C : Capsule n) (dims : Fin m → Fin n) : Capsule m where
  c := fun i => C.c (dims i)
  g := fun i => C.g (dims i)
  r := C.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
