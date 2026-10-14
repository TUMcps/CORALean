module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `withinTol`

`global/functions/matlab/validate/check/withinTol.m` for two scalars: the distance is at most
`tol`, absolutely or relative to the smaller magnitude (written without the division, which
differs only where the smaller magnitude is `0` and the absolute test already decides), or both
are the same infinity.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.withinTol (tol : ℝ) (a b : EReal) : Prop :=
  (∃ x y : ℝ, a = x ∧ b = y ∧ (|x - y| ≤ tol ∨ |x - y| ≤ tol * min |x| |y|)) ∨
    (a = b ∧ (a = ⊤ ∨ a = ⊥))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
