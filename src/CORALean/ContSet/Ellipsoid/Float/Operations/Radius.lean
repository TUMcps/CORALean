module

public import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb

@[expose] public section

/-!
# `Ellipsoid.radius`, over a floating-point scalar

An upper bound on CORA's `radius` (the largest semi-axis, `sqrt(max(eig(Q)))`), which needs an
eigenvalue no float computes: `normUb` of the ellipsoid moved to the origin, the Frobenius norm
of `G` plus the length of the error box's largest magnitudes, rounded up. The ellipsoid lies in
the Euclidean ball of this radius about the stored center; it is not the smallest such ball.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` is the precision of the upward square roots, as in `normUb`. -/
def Ellipsoid.radius (p : ℕ) (E : Ellipsoid 𝕋 n) : 𝕋 :=
  let centered : Ellipsoid 𝕋 n := { E with c := fun _ => zero }
  centered.normUb p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
