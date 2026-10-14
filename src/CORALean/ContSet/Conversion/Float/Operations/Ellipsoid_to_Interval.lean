module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a box, over a floating-point scalar — the construction

`Ellipsoid.interval` is the construction; `Ellipsoid_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box, given one proposed length per coordinate. -/
def Ellipsoid.interval (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => addDown (subDown (E.c i) (absolute (s i))) (E.I_error.inf i)
  sup := fun i => addUp (addUp (E.c i) (absolute (s i))) (E.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
