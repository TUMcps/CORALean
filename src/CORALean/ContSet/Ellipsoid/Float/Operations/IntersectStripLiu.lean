module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripGollamudi

@[expose] public section

/-!
# `Ellipsoid.intersectStripLiu`, over a floating-point scalar

The corrected Liu2016 update (CORA's `@ellipsoid/intersectStrip`, method `'Liu2016'`; real layer
`Real.Ellipsoid.intersectStripLiu`) for **one** measurement row `c` and a scalar `V > 0`, at
`σ²_prev = 1`, by reduction to the float Gollamudi update. The measurement set
`(y - c x)² / V ≤ 1` is the strip `|c x - y| ≤ √V`, and at `σ²_prev = 1` the Liu fusion with
weight `λ` is the Gollamudi fusion with `φ = √V` at `λ' = λ / (λ + V (1 - λ))`. So this is a thin
wrapper: `φ = sqrtUp V` (an upward root only widens the strip) and `λ'` with directed rounding;
the float Gollamudi theorem has no hypothesis on its weight, so `λ'` need not be exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Liu update of `E` (level `σ²_prev = 1`) by the row `c`, the scalar `V` and the
measurement `y`, at the weight `lam`; `steps` Newton steps for the square roots. -/
def Ellipsoid.intersectStripLiu (steps : ℕ) (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n) (V y lam : 𝕋) :
    Ellipsoid 𝕋 n :=
  let φ : 𝕋 := sqrtUp steps V  -- `φ = √V`, rounded up
  let lam' : 𝕋 := divDown lam (addUp lam (mulUp V (subUp one lam)))  -- `λ / (λ + V (1 - λ))`
  Ellipsoid.intersectStripGollamudi steps E c φ y lam'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
