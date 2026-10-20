module

public import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair

@[expose] public section

/-!
# An inverted pair is inverted both ways

The test checks each direction, so it is symmetric.

## Inputs
* `Q` – H-polytope
* `i` – index below `Q.m`
* `j` – index below `Q.m`

## Hypotheses
* `h` – rows `i` and `j` of `Q` are an inverted pair

## Conclusion
* an inverted pair is inverted both ways
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isInvertedPair_symm {Q : HPolytope 𝕋 (Vec 𝕋 n)} {i j : Fin Q.m}
    (h : HPolytope.isInvertedPair Q i j = true) :
    HPolytope.isInvertedPair Q j i = true := by
  simp only [HPolytope.isInvertedPair, Bool.and_eq_true] at h ⊢
  tauto

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
