module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# The nominal center

The center of the nominal ellipsoid is the stored one read as reals, positive semi-definite `Q` or
not: CORA's constructor keeps it either way.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The nominal ellipsoid's center is the stored one, positive semi-definite `Q` or not. -/
theorem Ellipsoid.nominal_q [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).ellipsoid.q = toRealVec E.q := by
  show (Real.Ellipsoid.ofShape _ _).q = _
  unfold Real.Ellipsoid.ofShape
  split <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
