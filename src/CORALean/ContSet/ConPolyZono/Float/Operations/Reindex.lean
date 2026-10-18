module

public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.reindex` over a floating-point scalar

Center, both generator blocks' rows and the error box relabelled, and nothing
rounds: a permutation moves stored floats without arithmetic. The exponents and
the constraints live on the factors, which a relabelling of the coordinates does
not touch, so they are kept.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.reindex (e : Fin m ≃ Fin n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 m) where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  m := cPZ.m
  q := cPZ.q
  c := fun i => cPZ.c (e i)
  G := fun j i => cPZ.G j (e i)
  E := cPZ.E
  GI := fun j i => cPZ.GI j (e i)
  A := cPZ.A
  b := cPZ.b
  b_error := cPZ.b_error
  R := cPZ.R
  I_error := cPZ.I_error.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
