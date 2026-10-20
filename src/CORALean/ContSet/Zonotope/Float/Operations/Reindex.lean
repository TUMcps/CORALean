module

public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.reindex` over a floating-point scalar

Center, generator rows and error box all relabelled, and nothing rounds: a
permutation moves stored floats without arithmetic. The generator index is
untouched — only the coordinate axis moves, which is why the row index alone
carries `e`.

## Inputs
* `e` – coordinate equivalence
* `Z` – zonotope

## Output
* zonotope with relabelled coordinates
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reindex (e : Fin m ≃ Fin n) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 m) where
  h := Z.h
  c := fun i => Z.c (e i)
  G := fun j i => Z.G j (e i)
  I_error := Z.I_error.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
