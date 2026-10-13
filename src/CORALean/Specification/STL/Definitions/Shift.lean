import Mathlib.Data.NNReal.Defs

/-!
# The shift operator

`⟨ξ⟩ₐ(t) := ξ(t + a)` of [1, Sec. 2.2] for a trace and of [1, Def. 2] for a reach sequence:
one operator on any function of time, `ℝ≥0` being the paper's `ℝ≥0`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨f⟩ₐ`, the function `f` shifted in time by `a`. -/
abbrev Time.shift {α : Type*} (f : ℝ≥0 → α) (a : ℝ≥0) : ℝ≥0 → α := fun t => f (t + a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
