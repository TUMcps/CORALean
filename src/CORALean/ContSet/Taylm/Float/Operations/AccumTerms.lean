module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerm

@[expose] public section

/-!
# `Taylm.accumTerms`

The terms of a list added one after the other into a sorted term list (`Taylm.accumTerm`), as
CORA.cpp adds the terms of one model into the map of another, and the bounds of the roundings
summed, rounded up.

## Inputs
* `L` – term list, sorted by exponents
* `M` – terms to add, in order

## Output
* the sorted term list with every term of `M` added, and a bound of the roundings
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.accumTerms (L M : List (𝕋 × (Fin n → ℕ))) : List (𝕋 × (Fin n → ℕ)) × 𝕋 :=
  M.foldl (fun acc a =>
    let r := Taylm.accumTerm acc.1 a.1 a.2
    (r.1, addUp acc.2 r.2)) (L, zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
