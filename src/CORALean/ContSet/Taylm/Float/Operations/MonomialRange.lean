module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.monomialRange`

The range of a monomial over the box `[-1, 1]ⁿ` as CORA's `interval` with method `'int'` takes
it: `[1, 1]` for the constant monomial, `[-1, 1]` if some exponent is odd, `[0, 1]` otherwise.

## Inputs
* `e` – exponents of the monomial

## Output
* interval holding the monomial on the box
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

def Taylm.monomialRange (e : Fin n → ℕ) : Interval 𝕋 :=
  if Real.Taylm.degree e = 0 then ⟨one, one⟩
  else if ∃ k, e k % 2 = 1 then ⟨neg one, one⟩
  else ⟨zero, one⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
