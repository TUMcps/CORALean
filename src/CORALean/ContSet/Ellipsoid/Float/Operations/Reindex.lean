module

public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.reindex` over a floating-point scalar

Center, generator rows and error box relabelled, and nothing rounds: a permutation
moves stored floats without arithmetic. The generator index is untouched, only
the coordinate axis moves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.reindex (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m where
  k := E.k
  c := fun i => E.c (e i)
  G := fun i j => E.G (e i) j
  I_error := E.I_error.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
