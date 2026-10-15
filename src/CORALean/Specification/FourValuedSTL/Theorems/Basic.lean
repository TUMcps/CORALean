module

public import CORALean.Specification.FourValuedSTL.Definitions.Basic

@[expose] public section

/-!
# `FourValuedSTL/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

`satBool_eq_true_iff` says that the Boolean signal `⟦φ⟧_ξ` of [1, Sec. 2.5] is `⊤` where the
formula is satisfied.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open scoped NNReal


-- =======================  `FourValuedSTL.Formula.satBool_eq_true_iff`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `⟦φ⟧_ξ(t) = ⊤` iff `φ` holds of `ξ` at `t`, [1, Sec. 2.5]. -/
theorem FourValuedSTL.Formula.satBool_eq_true_iff {X : Type} (φ : FourValuedSTL.Formula X)
    (ξ : ℝ≥0 → X) (t : ℝ≥0) : φ.satBool ξ t = true ↔ φ.Sat ξ t := by
  simp [FourValuedSTL.Formula.satBool]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
