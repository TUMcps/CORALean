module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Zonotope.radiusCora`

CORA.cpp's `@zonotope/radius`: the smaller of the sum of the generator lengths and the Euclidean
norm of the half-widths of the box `interval(Z)`. As `Zonotope.radius` it is a radius about the
stored center and pays for the error box by its largest magnitude, but the box is built the way
CORA builds it, as the ends `c ± (rowSum |G| + err)` rounded outward and half their difference,
`(sup - inf) / 2`, not the row sum alone. At `nearest` with a zero error box that is CORA's value
bit for bit. The half difference is at least the row sum plus the error, so the radius stays above
every distance to the center.

## Inputs
* `k` – Newton steps for the norm
* `Z` – zonotope

## Output
* radius of a ball about the center enclosing the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.radiusCora (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let err := fun i => maximum (absolute (Z.I_error.inf i)) (absolute (Z.I_error.sup i))
  let errLength := normUp k err
  let lengths := addUp (sumUp fun j => normUp k (Z.G j)) errLength
  -- the box `c ± (rowSum |G| + err)`, its ends rounded outward
  let reach := fun i => addUp (CORALean.Float.radius (fun i j => Z.G j i) i) (err i)
  let sup := fun i => addUp (Z.c i) (reach i)
  let inf := fun i => subDown (Z.c i) (reach i)
  let box := normUp k fun i => half (subUp (sup i) (inf i))
  minimum lengths box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
