module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# Two polytopes with the same nominal part and box denote the same set

The set is the nominal part plus the box, so equal parts give equal sums.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.construct_congr {P Q : HPolytope 𝕋 (Vec 𝕋 n)}
    (hN : P.nominal.construct = Q.nominal.construct)
    (hE : P.I_error.construct = Q.I_error.construct) : P.construct = Q.construct := by
  -- the set is `nominal + box`, and both summands agree
  show P.nominal.construct + P.I_error.construct = Q.nominal.construct + Q.I_error.construct
  rw [hN, hE]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
