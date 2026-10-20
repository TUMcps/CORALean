module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow

The Schur form `[[1, (x - q)ᵀ], [x - q, Q]] ⪰ 0`, written `A₀ + Σᵢ xᵢ Aᵢ ⪰ 0` with
`A₀ = [[1, -qᵀ], [-q, Q]]` and `Aᵢ` the border at `i`, over the free variables `x` themselves
(`c = 0`, `G = I`). By the Schur complement it says `(x - q)(x - q)ᵀ ⪯ Q`, which is `x` in the
ellipsoid for every positive semi-definite `Q`, degenerate ones included
(`Theorems/EllipsoidPosSemidefSpectraShadowIff`). No inverse and no square root, so the float
layer stores the same matrices exactly. CORA's `spectraShadow` writes the set as
`{x | 1 - (x-q)ᵀ Q⁻¹ (x-q) ≥ 0}` from `chol(inv(Q))`, and by an SVD when `Q` is singular.

## Inputs
* `E` – ellipsoid

## Output
* Schur-form spectrahedral shadow of the ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid as the shadow of the Schur form `[[1, (x - q)ᵀ], [x - q, Q]] ⪰ 0`. -/
def Ellipsoid.spectraShadow (E : Ellipsoid n) : SpectraShadow (Vec ℝ n) where
  k := n + 1
  m := n
  A₀ := Matrix.of fun p r =>
    Fin.cases (Fin.cases 1 (fun j => -E.q j) r) (fun i => Fin.cases (-E.q i) (fun j => E.Q i j) r) p
  A := fun i => Matrix.of fun p r =>
    if (p = 0 ∧ r = i.succ) ∨ (p = i.succ ∧ r = 0) then 1 else 0
  c := 0
  G := fun i => Pi.single i 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
