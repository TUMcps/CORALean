import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape

/-!
# `Ellipsoid.intersectStripLiu`

CORA's `@ellipsoid/intersectStrip` (method `'Liu2016'`, `aux_methodLiu2016`) for the state set
`{x | (x - c)ᵀ Q⁻¹ (x - c) ≤ σ²_prev}` and the measurement set `{x | (y - C x)ᵀ V⁻¹ (y - C x) ≤ 1}`
(`C` is `m × n`, `V = sys.V`), at the weight `λ` (CORA's `λ` from Thm. 3 and the eigenvalue of
`barV C Q Cᵀ barVᵀ`, and the trigger `σ²_prev + δᵀδ > 1`, are the caller's), corrected so that
it encloses the intersection (`intersectStripLiu_outer`). Every point of the intersection has
`(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ (y - C x)ᵀ V⁻¹ (y - C x) ≤ (1 - λ) σ²_prev + λ`, which completes
to `(x - c*)ᵀ ((1 - λ) Q⁻¹ + λ Cᵀ V⁻¹ C) (x - c*) ≤ σ²`. As the code computes them: `δ = y - C c`,
`Q_tmp = V/λ + C Q Cᵀ/(1 - λ)` (Eq. 27), `K = Q Cᵀ Q_tmp⁻¹/(1 - λ)` (Eq. 26),
`σ² = (1 - λ) σ²_prev + λ - δᵀ Q_tmp⁻¹ δ` (Eq. 25) and the centre `c* = c + K δ` (Eq. 23). The
correction: `((1 - λ) Q⁻¹ + λ Cᵀ V⁻¹ C)⁻¹ = (I - K C) Q/(1 - λ)`, where the code's shape (Eq. 24)
is `(1 - λ)(I - K C) Q`; the result is the level-`σ²` set of it, the shape `σ² (I - K C) Q/(1 - λ)`.
`intersectStripLiu1D` is the update as the code computes it, with its counterexample.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.intersectStripLiu (Q : Mat ℝ n n) (c : Vec ℝ n) (C : Mat ℝ m n)
    (V : Mat ℝ m m) (y : Vec ℝ m) (σsqPrev lam : ℝ) : Ellipsoid n :=
  let δ := y - C *ᵥ c  -- `delta`
  let Qtmp := (1 / lam) • V + (1 / (1 - lam)) • (C * Q * Cᵀ)  -- `Q_tmp`, eq. (27)
  let QtmpInv := Qtmp⁻¹  -- `Q_tmp_inv`
  let K := (1 / (1 - lam)) • (Q * Cᵀ * QtmpInv)  -- `K`, eq. (26)
  let σsq := (1 - lam) * σsqPrev + lam - δ ⬝ᵥ QtmpInv *ᵥ δ  -- `sigma_sq`, eq. (25)
  let Q' := (1 / (1 - lam)) • ((1 - K * C) * Q)  -- eq. (24); the code has `(1-lambda)*`
  let c' := c + K *ᵥ δ  -- new centre, eq. (23)
  Ellipsoid.ofShape (σsq • Q') c'  -- the level-`sigma_sq` set of `Q'`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
