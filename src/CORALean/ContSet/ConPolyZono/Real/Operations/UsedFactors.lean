module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.usedFactors`

The factors either block still reads. `appendE` puts both exponent matrices
over the shared factors, so this is `PolyZonotope.usedFactors` of one matrix
and denotes the union of the two used sets.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `q` – number of constraint generators
* `E` – exponent matrix
* `R` – constraint exponent matrix

## Output
* set of factors either block still reads
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors either block still reads. `appendE` puts both exponent matrices
over the shared factors, so this is `PolyZonotope.usedFactors` of one matrix and
denotes the union of the two used sets. -/
def ConPolyZono.usedFactors {p h q : ℕ} (E : Fin p → Fin h → ℕ) (R : Fin p → Fin q → ℕ) :
    Finset (Fin p) :=
  PolyZonotope.usedFactors (ConPolyZono.appendE E R)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
