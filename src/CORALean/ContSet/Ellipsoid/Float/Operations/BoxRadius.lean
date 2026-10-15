module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# The half-widths of an ellipsoid's box

CORA's `interval(E)` is `q ± sqrt(diag(Q))`; these are the half-widths, each square root rounded up
and taken of the diagonal entry floored at `0`, so that they bound the nominal part whatever `Q`
was stored (`abs_sub_le_boxRadius`; for a positive semi-definite `Q` the real fact is
`Real.Ellipsoid.abs_sub_le_sqrt_diag`). An operation that cannot certify `Q` positive
semi-definite falls back to this box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sqrt(max(0, diag(Q)))`, rounded up; `p` Newton steps per root. -/
def Ellipsoid.boxRadius (p : ℕ) (E : Ellipsoid 𝕋 n) : Vec 𝕋 n :=
  fun i => sqrtUp p (maximum zero (E.Q i i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
