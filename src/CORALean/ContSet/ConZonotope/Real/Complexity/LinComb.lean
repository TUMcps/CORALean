import CORALean.ContSet.ConZonotope.Real.Operations.LinComb

/-!
# `ConZonotope.linComb`'s counts

`linComb`'s generator count: the two operands' plus the one fresh coefficient
naming the interpolation parameter, exactly as a zonotope's `linComb` adds one
generator. The equality count carries over unchanged — `halfScaled` and
`comap` both leave it alone, and neither block's unit box contributes one. The
inequality count does grow, by `2(h₁+h₂)`: each block's own unit box, pulled
back onto its slice of the concatenated coefficients, `[1, Thm. 5]` spends the
same `2(h₁+h₂)` slack coefficients but as equalities instead. `rfl` against
the structure instance in `Operations/LinComb.lean`, `me` after unfolding the
zero the unit box's own equality count contributes.

## References

* [1] V. Raghuraman, J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". arXiv:2009.06039, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linComb_h (C₁ C₂ : ConZonotope α) :
    (C₁.linComb C₂).h = C₁.h + C₂.h + 1 := rfl

theorem ConZonotope.linComb_P_m (C₁ C₂ : ConZonotope α) :
    (C₁.linComb C₂).P.m = (C₁.h + C₁.h + C₁.P.m) + (C₂.h + C₂.h + C₂.P.m) := rfl

theorem ConZonotope.linComb_P_me (C₁ C₂ : ConZonotope α) :
    (C₁.linComb C₂).P.me = C₁.P.me + C₂.P.me := by
  show 0 + C₁.P.me + (0 + C₂.P.me) = C₁.P.me + C₂.P.me
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
