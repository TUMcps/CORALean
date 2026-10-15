module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic

@[expose] public section

/-!
# `FiniteKleeneSignalBuilder/Theorems`: small theorems

One section per theorem, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================  `FiniteKleeneSignalBuilder.comb_eq_ff_iff`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The property is false exactly where it can be false and cannot be true. -/
theorem FiniteKleeneSignalBuilder.comb_eq_ff_iff (x y : Bool) :
    FiniteKleeneSignalBuilder.comb x y = .ff ↔ x = false ∧ y = true := by
  cases x <;> cases y <;> simp [FiniteKleeneSignalBuilder.comb]


-- ========================  `FiniteKleeneSignalBuilder.comb_eq_tt_iff`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The property is true exactly where it can be true and cannot be false. -/
theorem FiniteKleeneSignalBuilder.comb_eq_tt_iff (x y : Bool) :
    FiniteKleeneSignalBuilder.comb x y = .tt ↔ x = true ∧ y = false := by
  cases x <;> cases y <;> simp [FiniteKleeneSignalBuilder.comb]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
