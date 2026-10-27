module

public import CORALean.ContSet.Interval.Float.Operations.CenterBoxMat
public import CORALean.ContSet.Interval.Float.Operations.RadiusMat
public import CORALean.ContSet.Interval.Real.Definitions.NormType
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Interval.matNorm`, over a floating-point scalar

CORA's `norm(intMat, type)`: the norm of `abs(center) + rad`, for the types `1`, `Inf` and
`'fro'`, rounded up. The center is bracketed by `centerBoxMat` and its absolute value taken at the
larger end; column and row sums add up, the maximum is exact, and the Frobenius norm takes
`sqrtUp` of the sum of squares with `steps` Newton steps.

## Inputs
* `steps` – number of Newton steps of the square root
* `p` – norm type
* `I` – interval matrix

## Output
* upper bound of the norm of `abs(center) + rad`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Entry `(i, j)` of `abs(center) + rad`, rounded up: the larger end of the bracketed center in
absolute value, plus the half-width. -/
def Interval.aux_normEntry (I : Interval (Mat 𝕋 m n)) (i : Fin m) (j : Fin n) : 𝕋 :=
  addUp (maximum (absolute (I.centerBoxMat.inf i j)) (absolute (I.centerBoxMat.sup i j)))
    (I.radiusMat i j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The norm of `type` at the rounded-up `abs(center) + rad`. -/
def Interval.matNorm (steps : ℕ) (p : Real.Interval.NormType) (I : Interval (Mat 𝕋 m n)) : 𝕋 :=
  match p with
  | .one => maximumOver fun j => sumUp fun i => I.aux_normEntry i j
  | .inf => maximumOver fun i => sumUp fun j => I.aux_normEntry i j
  | .fro => sqrtUp steps (sumUp fun i => sumUp fun j =>
      mulUp (I.aux_normEntry i j) (I.aux_normEntry i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
