module

public import CORALean.Specification.STL.Definitions.NnfRewrite
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenOr
public import CORALean.Specification.STL.Theorems.RewriteFinOpenOr

@[expose] public section

/-!
# A disjunction rewrites to sampled time

[1, Lemma 4]: `φ ∨ ψ` rewrites if `φ` and `ψ` do, by [1, Table 1]'s rows for `G_I` and `F_I` of `∨`.

## Inputs
* `φ` – left formula
* `ψ` – right formula

## Hypotheses
* `hφ` – the left formula rewrites to sampled time
* `hψ` – the right formula rewrites to sampled time

## Conclusion
* the disjunction rewrites to sampled time

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

theorem STL.Nnf.hasSampledRewrite_or {φ ψ : STL.Nnf X} (hφ : φ.HasSampledRewrite)
    (hψ : ψ.HasSampledRewrite) : -- --- CONCL ---
    (STL.Nnf.or φ ψ).HasSampledRewrite := by -- --- PROOF ---
  obtain ⟨⟨sT₁, hT₁⟩, ⟨sF₁, hF₁⟩, ⟨sG₁, hG₁⟩⟩ := hφ
  obtain ⟨⟨sT₂, hT₂⟩, ⟨sF₂, hF₂⟩, ⟨sG₂, hG₂⟩⟩ := hψ
  refine ⟨⟨.or sT₁ sT₂, fun ξ h => ?_⟩, ⟨.or sF₁ sF₂, fun ξ h => ?_⟩,
    ⟨.or sG₁ sG₂, fun ξ h => ?_⟩⟩
  · exact (show _ ∨ _ from h).imp (hT₁ ξ) (hT₂ ξ)
  · refine STL.rewrite_finOpen_or φ.toFormula ψ.toFormula ξ ?_
    exact (show _ ∨ _ from h).imp (hF₁ ξ) (hF₂ ξ)
  · refine STL.rewrite_globOpen_or φ.toFormula ψ.toFormula ξ ?_
    exact (show _ ∨ _ from h).imp (hG₁ ξ) (hG₂ ξ)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
