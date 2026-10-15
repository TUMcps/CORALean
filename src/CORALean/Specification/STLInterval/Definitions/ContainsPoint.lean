module

public import CORALean.Specification.STLInterval.Definitions.WithinTol

@[expose] public section

/-!
# `contains_` of a point

`@stlInterval/contains_.m`, the numeric branch: strictly between the bounds, or at a closed bound
(up to `tol`). The empty interval contains nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.containsPoint (tol : ℝ) : STLInterval → ℝ → Prop
  | .empty, _ => False
  | .nonempty l u lc rc _ _ _ _, t =>
    (l < t ∧ (t : EReal) < u) ∨ (lc = true ∧ withinTol tol l t) ∨
      (rc = true ∧ withinTol tol u t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
