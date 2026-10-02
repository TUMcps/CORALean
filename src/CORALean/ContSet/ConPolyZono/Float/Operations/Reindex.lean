import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.reindex` over a floating-point scalar

Centre, both generator blocks' rows and the error box relabelled, and nothing
rounds: a permutation moves stored floats without arithmetic. The exponents and
the constraints live on the factors, which a relabelling of the coordinates does
not touch, so they are kept.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.reindex (e : Fin m ≃ Fin n) (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 m where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := fun i => cPZ.c (e i)
  G := fun i j => cPZ.G (e i) j
  E := cPZ.E
  GI := fun i j => cPZ.GI (e i) j
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC
  err := cPZ.err.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
