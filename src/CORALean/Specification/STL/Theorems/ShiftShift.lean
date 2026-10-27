module

public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# Shifting twice

`⟨⟨f⟩ₐ⟩_b = ⟨f⟩_{b+a}`, which every row of [1, Table 1] that nests a shift needs.

## Inputs
* `α` – value type
* `f` – function of time
* `a` – first shift
* `b` – second shift

## Hypotheses
* none

## Conclusion
* shifting twice equals shifting by the sum

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Time.shift_shift {α : Type*} (f : ℝ≥0 → α) (a b : ℝ≥0) :
    Time.shift (Time.shift f a) b = Time.shift f (b + a) := by
  funext t
  show f (t + b + a) = f (t + (b + a))
  rw [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
