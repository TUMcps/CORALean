module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.Basic

@[expose] public section

/-!
# `prev & I` over floats keeps the point

The meet of the previous interval with an interval that holds a point holds it still, and lies
inside the previous interval: the exact `max` and `min` of the stored bounds.

## Inputs
* `prev` – previous interval
* `I` – interval holding the point
* `s` – point

## Hypotheses
* `hs` – the previous interval holds the point
* `hI` – the interval holds the point

## Conclusion
* the meet holds the point and lies inside the previous interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `prev & I` holds `s` and lies inside `prev`. -/
theorem SyntaxTree.meet_containsFloat {prev I : Float.SyntaxTree.Dom 𝕋} {s : ℝ}
    (hs : prev.contains s) (hI : I.contains s) :
    Float.SyntaxTree.Dom.contains (Float.Interval.intersection prev I) s ∧
      Float.SyntaxTree.Dom.IsWithin (Float.Interval.intersection prev I) prev := by
  simp only [Float.SyntaxTree.Dom.contains, Float.SyntaxTree.Dom.IsWithin,
    Float.Interval.intersection, toReal_maximum, toReal_minimum]
  exact ⟨⟨max_le hs.1 hI.1, le_min hs.2 hI.2⟩, le_max_left _ _, min_le_left _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
