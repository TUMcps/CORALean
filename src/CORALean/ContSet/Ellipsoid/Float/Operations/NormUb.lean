module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.normUb`, over a floating-point scalar

CORA's `@ellipsoid/norm_.m` (type `2`), as an upper bound: `‖q‖₂`, plus `√(trace Q)` with each
diagonal entry floored at `0` (so that it bounds whatever `Q` was stored), plus the length of the
error box's largest magnitudes, every sum rounded up and the roots by `k` Newton steps
(`Global/Float/Sqrt`). Outer, as over ℝ: not CORA's `sqrt(max(eig(Q)))`.

## Inputs
* `k` – Newton steps of the root
* `E` – ellipsoid

## Output
* upper bound of the norm of the ellipsoid points
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.normUb (k : ℕ) (E : Ellipsoid 𝕋 n) : 𝕋 :=
  let err := fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i))
  let trace := sqrtUp k (sumUp fun i => maximum zero (E.Q i i))
  addUp (addUp (normUp k E.q) trace) (normUp k err)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
