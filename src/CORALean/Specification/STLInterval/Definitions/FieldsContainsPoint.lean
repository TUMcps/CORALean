module

public import CORALean.Specification.STLInterval.Definitions.Fields

@[expose] public section

/-!
# `contains_` of a point, on the fields of an object

The numeric branch of `@stlInterval/contains_.m` at `tol = 0`, read off the stored fields: strictly
between the bounds, or at a closed bound; a comparison with a `NaN` bound is false, and the empty
object (`none`) contains nothing.

## Inputs
* none

## Output
* the interval given by its fields contains the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.fieldsContainsPoint : Option (STLInterval.Fields 𝕋) → ℝ → Prop
  | none, _ => False
  | some ⟨l, u, lc, rc⟩, t =>
    (((toReal l : ℝ) : EReal) < t ∧ ∃ x, u = some x ∧ (t : EReal) < toEReal x) ∨
      (lc = true ∧ ((toReal l : ℝ) : EReal) = t) ∨
      (rc = true ∧ ∃ x, u = some x ∧ toEReal x = (t : EReal))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
