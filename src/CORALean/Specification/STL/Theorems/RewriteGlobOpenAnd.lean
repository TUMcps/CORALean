module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd

@[expose] public section

/-!
# Rewriting, `G_I` of a conjunction

[1, Table 1] `G_I(φ₁ ∧ φ₂) ⇐ G_I φ₁ ∧ G_I φ₂`.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `ξ` – trace

## Hypotheses
* `h` – always holds for both formulas

## Conclusion
* always of the conjunction holds

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

theorem STL.rewrite_globOpen_and (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.globOpen 1 φ₂)).Satisfies ξ) :
    (STL.Formula.globOpen 1 (φ₁.and φ₂)).Satisfies ξ := by
  simp only [STL.Formula.sat_and, STL.Formula.Satisfies] at h ⊢
  exact fun t h₀ h₁ => ⟨h.1 t h₀ h₁, h.2 t h₀ h₁⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
