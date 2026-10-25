module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `ConPolyZono.padE`

An exponent matrix widened by fresh factors that none of its monomials uses:
what a constraint block keeps when an operation adds factors beside the ones it
was written against.

`PolyZonotope.padE` read at a constraint's exponent matrix rather than at a
generator block, and the same function: a constraint and a generator are two
readings of one factor vector, so widening that vector is one operation. The
name is kept because a caller reaching for it here is padding constraints.

## Inputs
* `p` – number of factors
* `q` – number of columns
* `R` – exponent matrix
* `r` – number of added factors

## Output
* the exponent matrix with zero rows appended
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Not the constraint's work (generators): `E` with the slack factors of `relax` and
`absorbRounding` appended; the constraint side is `PolyLevelSet.relax`. -/
def ConPolyZono.padE {p q : ℕ} (R : Fin p → Fin q → ℕ) (r : ℕ) :
    Fin (p + r) → Fin q → ℕ :=
  PolyZonotope.padE R r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
