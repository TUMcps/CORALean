module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Rewriting, `F_I` of a disjunction

[1, Table 1] `F_I(φ₁ ∨ φ₂) ⇐ F_I φ₁ ∨ F_I φ₂`.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `ξ` – trace

## Hypotheses
* `h` – one of the eventually formulas holds

## Conclusion
* eventually of the disjunction holds

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

theorem STL.rewrite_finOpen_or (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.finOpen 1 φ₁).or (STL.Formula.finOpen 1 φ₂)).Satisfies ξ) :
    (STL.Formula.finOpen 1 (φ₁.or φ₂)).Satisfies ξ := by
  simp only [STL.Formula.Satisfies] at h ⊢
  rcases h with ⟨s, hs₀, hs₁, hs⟩ | ⟨s, hs₀, hs₁, hs⟩
  · exact ⟨s, hs₀, hs₁, Or.inl hs⟩
  · exact ⟨s, hs₀, hs₁, Or.inr hs⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
