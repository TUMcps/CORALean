module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Rewriting, `G_I` of a disjunction

[1, Table 1] `G_I(φ₁ ∨ φ₂) ⇐ G_I φ₁ ∨ G_I φ₂`.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `ξ` – trace

## Hypotheses
* `h` – always holds for one of the formulas

## Conclusion
* always of the disjunction holds

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
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

theorem STL.rewrite_globOpen_or (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₁).or (STL.Formula.globOpen 1 φ₂)).Satisfies ξ) :
    (STL.Formula.globOpen 1 (φ₁.or φ₂)).Satisfies ξ := by
  simp only [STL.Formula.Satisfies] at h ⊢
  rcases h with h | h
  · exact fun t h₀ h₁ => Or.inl (h t h₀ h₁)
  · exact fun t h₀ h₁ => Or.inr (h t h₀ h₁)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
