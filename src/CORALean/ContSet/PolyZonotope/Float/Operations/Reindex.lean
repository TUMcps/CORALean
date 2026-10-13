import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.reindex` over a floating-point scalar

Centre, both generator blocks' rows and the error box relabelled, and nothing
rounds: a permutation moves stored floats without arithmetic. The exponent matrix
indexes factors and generators, not coordinates, so it is kept.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.reindex (e : Fin m ≃ Fin n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := fun i => pZ.c (e i)
  G := fun j i => pZ.G j (e i)
  E := pZ.E
  GI := fun j i => pZ.GI j (e i)
  err := pZ.err.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
