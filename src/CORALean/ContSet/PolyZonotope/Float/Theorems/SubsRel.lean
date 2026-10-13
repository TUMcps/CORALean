import CORALean.ContSet.PolyZonotope.Float.Operations.SubsMul
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsMul
import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# A term list brackets an exact one

The float terms `subsMul`, `subsPow`, `subsXprod` and `subsTerms` build carry a bracket for each
coefficient, not the exact real one the exact layer's lists carry. `subsRel A A'` says the lists
have the same length, the same exponents, and each coefficient of `A'` is between the floats of
the matching term of `A`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsRel (A : List ((𝕋 × 𝕋) × (Fin p → ℕ))) (A' : List (ℝ × (Fin p → ℕ))) : Prop :=
  List.Forall₂ (fun s t => s.2 = t.2 ∧ toReal s.1.1 ≤ t.1 ∧ t.1 ≤ toReal s.1.2) A A'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
