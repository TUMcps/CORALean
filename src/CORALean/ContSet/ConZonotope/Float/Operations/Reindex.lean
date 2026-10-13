import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.reindex` over a floating-point scalar

Centre, generator rows and error box relabelled, and nothing rounds: a permutation
moves stored floats without arithmetic. The constraints live on the coefficient
space, which a relabelling of the coordinates does not touch, so `P` is kept.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.reindex (e : Fin m ≃ Fin n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 m) where
  h := cZ.h
  c := fun i => cZ.c (e i)
  G := fun j i => cZ.G j (e i)
  P := cZ.P
  E := cZ.E.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
