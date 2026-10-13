import CORALean.Specification.STL.STL

/-!
# Conjunction in STL

`φ ∧ ψ` is an abbreviation for `¬(¬φ ∨ ¬ψ)` ([1, Sec. 2.2] says only that the other operators are
derived); this is that it means `∧`.

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

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_and (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (φ.and ψ).Sat ξ ↔ φ.Sat ξ ∧ ψ.Sat ξ := by
  simp [STL.Formula.and, STL.Formula.Sat]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
