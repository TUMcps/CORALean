import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair

/-!
# An inverted pair is inverted both ways

The test checks each direction, so it is symmetric.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isInvertedPair_symm {Q : HPolytope 𝕋 n} {i j : Fin Q.m}
    (h : HPolytope.isInvertedPair Q i j = true) :
    HPolytope.isInvertedPair Q j i = true := by
  simp only [HPolytope.isInvertedPair, Bool.and_eq_true] at h ⊢
  tauto

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
