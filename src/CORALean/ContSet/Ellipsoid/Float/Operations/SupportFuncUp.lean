module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.supportFuncUp`, over a floating-point scalar

CORA's `supportFunc_(E, a, 'upper')`, `aᵀq + √(aᵀ Q a)`, in CORA's arithmetic: the shift `aᵀq`
(`dotUp`), the quadratic form `aᵀ (Q a)` (`quadUp`, clamped at zero) under an upward square root,
and the error box's own bound in direction `a` (each coordinate at the end its sign picks), all
added upward. Where `Ellipsoid.nominalBoundDot` takes a proposed length `s` with `aᵀ Q a ≤ s²`,
this computes the length, so no check can fail.

## Inputs
* `k` – Newton steps of the square root
* `E` – ellipsoid
* `a` – direction

## Output
* upper bound of `aᵀx` over the points `x` of `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.supportFuncUp (k : ℕ) (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) : 𝕋 :=
  -- the shift of the center, `aᵀ q`
  let shift : 𝕋 := dotUp a E.q
  -- the spread `√(aᵀ Q a)`, the form clamped at zero
  let spread : 𝕋 := sqrtUp k (maximum zero (E.quadUp a))
  -- the error box in direction `a`: per coordinate the end the sign of `aᵢ` picks
  let err : 𝕋 := sumUp fun j =>
    maximum (mulUp (a j) (E.I_error.sup j)) (mulUp (a j) (E.I_error.inf j))
  addUp (addUp shift spread) err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
