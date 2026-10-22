module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.NoNaN
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `Ellipsoid.ellipsoidNormUb`, over a floating-point scalar

An upper bound on CORA's `@ellipsoid/ellipsoidNorm` (full-rank branch, `sqrt(pᵀ Q⁻¹ p)`), whose
solve `Q \ p` no rounded arithmetic does exactly. The caller proposes the solve `w` with `Q w = p`,
checked exactly in ℚ (`ToRat`); then `pᵀ Q⁻¹ p = pᵀ w`, rounded up and its square root rounded up.
`none` when the equation fails, or when `Q`, `p` or `w` holds a NaN: `toRat` reads it as the
number `1.5 · 2 ^ 1024`, of which the equation could hold. Of the nominal ellipsoid, as CORA's
(the shape matrix alone).

## Inputs
* `prec` – Newton steps of the root
* `E` – ellipsoid
* `p` – point
* `w` – solve of `Q w = p`

## Output
* upper bound of the ellipsoid norm of `p`, `none` if `Q w = p` fails
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps ToRat

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `prec` is the precision of the upward square root. -/
def Ellipsoid.ellipsoidNormUb (prec : ℕ) (E : Ellipsoid 𝕋 n) (p w : Vec 𝕋 n) : Option 𝕋 :=
  let image : Vec ℚ n := fun i => ∑ j, toRat (E.Q i j) * toRat (w j)
  let solves : Bool := (List.finRange n).all fun i => decide (image i = toRat (p i))
  let finite : Bool := noNaN (𝕋 := 𝕋) E.Q && noNaN (𝕋 := 𝕋) p && noNaN (𝕋 := 𝕋) w
  if solves && finite then some (sqrtUp prec (dotUp p w)) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
