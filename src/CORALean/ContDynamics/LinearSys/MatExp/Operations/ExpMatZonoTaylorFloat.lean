import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTermFloat
import CORALean.ContSet.Zonotope.Float.Operations.MatPlus

/-!
# `MatExp.expMatZonoTaylor`, over a floating-point scalar

`Real.MatExp.expMatZonoTaylor` rounded, the same recursion `i = 0 … η`, each partial sum
materialised before the next order joins it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.3.2]'s Taylor truncation as a float matrix zonotope, orders `0 … η`. -/
def MatExp.expMatZonoTaylor (M : Zonotope (Mat 𝕋 n n)) : ℕ → Zonotope (Mat 𝕋 n n)
  | 0 => MatExp.expMatZonoTerm M 0
  | k + 1 => (Zonotope.matPlus (MatExp.expMatZonoTerm M (k + 1))
      (MatExp.expMatZonoTaylor M k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
