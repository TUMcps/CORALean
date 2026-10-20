module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend

@[expose] public section

/-!
# `ConPolyZono.factorExtend`

A factor vector over the kept factors, read back over all of them by giving a
dropped factor the value zero — admissible, and read by no monomial of either
block.

## Inputs
* `p` – number of factors
* `h` – number of dependent generators
* `q` – number of constraint generators
* `E` – exponent matrix
* `R` – constraint exponent matrix
* `a` – values of the used factors
* `k` – factor index

## Output
* value of that factor, zero if dropped
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A factor vector over the kept factors, read back over all of them by giving a
dropped factor the value zero — admissible, and read by no monomial of either
block. -/
def ConPolyZono.factorExtend {p h q : ℕ} (E : Fin p → Fin h → ℕ) (R : Fin p → Fin q → ℕ)
    (a : Fin (ConPolyZono.usedFactors E R).card → ℝ) (k : Fin p) : ℝ :=
  PolyZonotope.factorExtend (ConPolyZono.appendE E R) a k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
