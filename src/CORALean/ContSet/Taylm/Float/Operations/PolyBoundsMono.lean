module

public import CORALean.ContSet.Taylm.Float.Operations.MonomialRange
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.TimesZeroInf

@[expose] public section

/-!
# `Taylm.polyBoundsMono`

The range of a term list over the box `[-1, 1]ⁿ`, CORA's method `'int'` as CORA.cpp computes
it: from `[0, 0]`, each term's coefficient times the range of its monomial
(`Taylm.monomialRange`, `Taylm.timesZeroInf`) added in the order of the list.

## Inputs
* `L` – term list

## Output
* interval holding the polynomial on the box
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

def Taylm.polyBoundsMono (L : List (𝕋 × (Fin n → ℕ))) : Interval 𝕋 :=
  Taylm.sumRanges (fun a => Taylm.timesZeroInf (Taylm.monomialRange a.2) ⟨a.1, a.1⟩)
    ⟨zero, zero⟩ L

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
