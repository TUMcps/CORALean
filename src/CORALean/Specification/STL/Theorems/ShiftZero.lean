module

public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# Shifting by nothing

`⟨f⟩₀ = f`: a trace shifted by zero is the trace, [1, Sec. 2.2].

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem Time.shift_zero {α : Type*} (f : ℝ≥0 → α) : Time.shift f 0 = f := by
  funext t
  show f (t + 0) = f t
  rw [add_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
