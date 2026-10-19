module

public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.reindex` over a floating-point scalar

The shape matrix's rows and columns, the center and the error box relabelled, and nothing rounds:
a permutation moves stored floats without arithmetic.

## Inputs
* `e` – equivalence of the coordinates
* `E` – ellipsoid

## Output
* `E` with its coordinates permuted by `e`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.reindex (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m where
  Q := fun i j => E.Q (e i) (e j)
  q := fun i => E.q (e i)
  I_error := E.I_error.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
