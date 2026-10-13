module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.normUb`, over a floating-point scalar

CORA's `@ellipsoid/norm_.m` (type `2`), as an upper bound: `‖q‖₂`, plus the Frobenius norm of `G`,
plus the length of the error box's largest magnitudes, every sum rounded up and the roots by `k`
Newton steps (`Global/Float/Sqrt`). Outer, as over ℝ: not CORA's `sqrt(max(eig(Q)))`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.normUb (k : ℕ) (E : Ellipsoid 𝕋 n) : 𝕋 :=
  let err := fun i => maximum (absolute (E.err.inf i)) (absolute (E.err.sup i))
  let frobenius := sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (E.G i j))
  addUp (addUp (normUp k E.q) frobenius) (normUp k err)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
