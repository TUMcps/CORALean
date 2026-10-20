module

public import CORALean.Specification.STL.Definitions.NnfRewrite
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenAnd
public import CORALean.Specification.STL.Theorems.RewriteFinOpenAnd
public import CORALean.Specification.STL.Theorems.SatAnd

@[expose] public section

/-!
# A conjunction rewrites to sampled time

[1, Lemma 4]: `φ ∧ ψ` rewrites if `φ` and `ψ` do, by [1, Table 1]'s rows for `G_I` and `F_I` of `∧`.

## Inputs
* `φ` – left formula
* `ψ` – right formula

## Hypotheses
* `hφ` – the left formula rewrites to sampled time
* `hψ` – the right formula rewrites to sampled time

## Conclusion
* the conjunction rewrites to sampled time

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

theorem STL.Nnf.hasSampledRewrite_and {φ ψ : STL.Nnf X} (hφ : φ.HasSampledRewrite)
    (hψ : ψ.HasSampledRewrite) : -- --- CONCL ---
    (STL.Nnf.and φ ψ).HasSampledRewrite := by -- --- PROOF ---
  obtain ⟨⟨sT₁, hT₁⟩, ⟨sF₁, hF₁⟩, ⟨sG₁, hG₁⟩⟩ := hφ
  obtain ⟨⟨sT₂, hT₂⟩, ⟨sF₂, hF₂⟩, ⟨sG₂, hG₂⟩⟩ := hψ
  refine ⟨⟨.and sT₁ sT₂, fun ξ h => ?_⟩, ⟨.or (.and sG₁ sF₂) (.and sF₁ sG₂), fun ξ h => ?_⟩,
    ⟨.and sG₁ sG₂, fun ξ h => ?_⟩⟩
  · -- `∧` of the two rewritings
    obtain ⟨h₁, h₂⟩ := (STL.Formula.sat_and _ _ _).1 h
    exact (STL.Formula.sat_and _ _ _).2 ⟨hT₁ ξ h₁, hT₂ ξ h₂⟩
  · -- row `F_I(φ ∧ ψ)`: one operand throughout the window, the other somewhere in it
    refine STL.rewrite_finOpen_and φ.toFormula ψ.toFormula ξ ?_
    rcases h with h | h
    · obtain ⟨h₁, h₂⟩ := (STL.Formula.sat_and _ _ _).1 h
      exact Or.inl ((STL.Formula.sat_and _ _ _).2 ⟨hG₁ ξ h₁, hF₂ ξ h₂⟩)
    · obtain ⟨h₁, h₂⟩ := (STL.Formula.sat_and _ _ _).1 h
      exact Or.inr ((STL.Formula.sat_and _ _ _).2 ⟨hF₁ ξ h₁, hG₂ ξ h₂⟩)
  · refine STL.rewrite_globOpen_and φ.toFormula ψ.toFormula ξ ?_
    obtain ⟨h₁, h₂⟩ := (STL.Formula.sat_and _ _ _).1 h
    exact (STL.Formula.sat_and _ _ _).2 ⟨hG₁ ξ h₁, hG₂ ξ h₂⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
