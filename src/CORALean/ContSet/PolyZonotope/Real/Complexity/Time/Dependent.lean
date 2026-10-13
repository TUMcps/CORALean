module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.dependentCost`

Asserted, not proved, and asserted to be zero: `Operations/Dependent.lean`
concatenates the two generator blocks and lays `identE` beside the exponent
matrix, and every entry of either is one the operand already held or a literal
`0` or `1`. Nothing is computed, so nothing is counted.

A zero is worth stating rather than leaving out. `quadMapCost` is
`quadMapDepCost` at the shifted counts and nothing more, and that is only true
because this conversion is free; a reader who cannot see the zero has to
rediscover it. What the conversion *does* cost the caller is size — `p + q`
factors and `h + q` dependent generators, proved in `Complexity/Space/Dependent.lean`
— and every count downstream is evaluated there.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.dependent` costs: nothing. Concatenation and the
identity exponent block are index and allocation work. -/
def PolyZonotope.dependentCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
