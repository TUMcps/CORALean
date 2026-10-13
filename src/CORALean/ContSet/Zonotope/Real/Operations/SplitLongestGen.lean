import CORALean.ContSet.Zonotope.Real.Operations.LongestGen
import CORALean.ContSet.Zonotope.Real.Operations.Split

/-!
# `Zonotope.splitLongestGen`

CORA's `splitLongestGen`: `split` at the generator `longestGen` picks. A zonotope with no
generator is its own two halves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along its longest generator. -/
noncomputable def Zonotope.splitLongestGen (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  match Z.longestGen with
  | some j => Z.split j
  | none => (Z, Z)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
