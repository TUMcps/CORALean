module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The error matrix `A - L C` as an interval matrix

The matrix `A - L C` of the observers' error dynamics, from the stored `A`, `L`, `C`: the product
`L C` by `Interval.matMul` and one directed subtraction per entry, so the interval matrix holds
the real `A - L C` (`errMatFloat_mem`).

## Inputs
* `A` – state matrix
* `L` – observer gain
* `C` – output matrix

## Output
* the error matrix as an interval matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `A - L C`, rounded outward. -/
def LinearSysDT.errMatFloat (A : Mat 𝕋 n n) (L : Mat 𝕋 n p) (C : Mat 𝕋 p n) :
    Interval (Mat 𝕋 n n) :=
  let LC : Interval (Mat 𝕋 n n) := Interval.matMul (Interval.point L) (Interval.point C)
  { inf := fun i j => subDown (A i j) (LC.sup i j)
    sup := fun i j => subUp (A i j) (LC.inf i j) }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
