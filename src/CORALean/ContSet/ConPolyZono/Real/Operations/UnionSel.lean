module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.unionSel`

The factor [1, Thm. 1] calls `α₁`: the one whose sign selects which operand a point
of the union comes from. Its partner `α₂`, which the constraint `α₁α₂ = 1` pins to
the same sign, is the factor after it and needs no name of its own.

[1] puts the two fresh factors first. Here they go last, as every other
operation in this directory puts fresh factors last, so that the two operands'
blocks keep the layout `plusE` gives them; identity is positional, and a
relabelling of factors changes nothing a set denotes.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The branch selector, the first of the two factors `union` adds. -/
def ConPolyZono.unionSel (p₁ p₂ : ℕ) : Fin (p₁ + p₂ + 2) := Fin.natAdd (p₁ + p₂) 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
