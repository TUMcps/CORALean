module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd

@[expose] public section

/-!
# Rewriting, `F_I` of a conjunction

[1, Table 1] `F_I(φ₁ ∧ φ₂) ⇐ (G_I φ₁ ∧ F_I φ₂) ∨ (F_I φ₁ ∧ G_I φ₂)`.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `ξ` – trace

## Hypotheses
* `h` – the rewritten disjunction of conjunctions holds

## Conclusion
* eventually of the conjunction holds

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

theorem STL.rewrite_finOpen_and (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X)
    (h : (((STL.Formula.globOpen 1 φ₁).and (STL.Formula.finOpen 1 φ₂)).or
      ((STL.Formula.finOpen 1 φ₁).and (STL.Formula.globOpen 1 φ₂))).Satisfies ξ) :
    (STL.Formula.finOpen 1 (φ₁.and φ₂)).Satisfies ξ := by
  simp only [STL.Formula.sat_and, STL.Formula.Satisfies] at h ⊢
  rcases h with ⟨hG, s, hs₀, hs₁, hs⟩ | ⟨⟨s, hs₀, hs₁, hs⟩, hG⟩
  · exact ⟨s, hs₀, hs₁, hG s hs₀ hs₁, hs⟩
  · exact ⟨s, hs₀, hs₁, hs, hG s hs₀ hs₁⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
