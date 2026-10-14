module

public import CORALean.Specification.STLInterval.Definitions.Fields

@[expose] public section

/-!
# `contains_` of a point, on the fields of an object

The numeric branch of `@stlInterval/contains_.m` at `tol = 0`, read off the stored fields: strictly
between the bounds, or at a closed bound; a comparison with a `NaN` bound is false, and the empty
object (`none`) contains nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.fieldsContainsPoint : Option STLInterval.Fields → ℝ → Prop
  | none, _ => False
  | some ⟨l, u, lc, rc⟩, t =>
    (l < t ∧ ∃ x, u = some x ∧ (t : EReal) < x) ∨ (lc = true ∧ l = t) ∨
      (rc = true ∧ u = some (t : EReal))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
