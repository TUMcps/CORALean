module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# The nominal shape matrix

CORA's constructor at the stored floats: `Q` read as reals where it is positive semi-definite,
`0` where the constructor refuses it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- The nominal shape matrix: `Q` read as reals where it is positive semi-definite, else `0`. -/
theorem Ellipsoid.nominal_Q_eq [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).ellipsoid.Q
      = if (toRealMat E.Q).PosSemidef then toRealMat E.Q else 0 := by
  show (Real.Ellipsoid.ofShape (toRealMat E.Q) (toRealVec E.q)).Q = _
  unfold Real.Ellipsoid.ofShape
  split_ifs <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
