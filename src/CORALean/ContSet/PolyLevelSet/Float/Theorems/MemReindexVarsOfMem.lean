module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.ReindexVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalReindexVars

@[expose] public section

/-!
# A point of `PolyLevelSet.reindexVars`, over a floating-point scalar

At an injective `f` that reaches every variable some monomial reads, `y ∘ f` meets the reindexed
rows within their slacks exactly when `y` meets `P`'s: the read-back rows are the exact layer's
reindexed rows (`Real.PolyLevelSet.eval_reindexVars`). The box is projected with them, so a point
of `P` gives one of the result; the converse fails, the dropped variables' bounds being lost.

## Inputs
* `P` – polynomial level set
* `n'` – new number of variables
* `f` – variable map
* `y` – real point

## Hypotheses
* `hf` – `f` is injective
* `h0` – unreached variables occur in no monomial
* `hy` – `y` lies in `P`

## Conclusion
* `y ∘ f` lies in the reindexed level set
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `y ∘ f` is in the reindexed set when `y` is in `P`. -/
theorem PolyLevelSet.mem_reindexVars_of_mem (P : PolyLevelSet 𝕋 n) {n' : ℕ} {f : Fin n' → Fin n}
    (hf : Function.Injective f) (h0 : ∀ k, k ∉ Set.range f → ∀ l, P.R k l = 0)
    {y : Vec ℝ n} (hy : y ∈ P.construct) :
    (fun k => y (f k)) ∈ (P.reindexVars f).construct := by -- --- PROOF ---
  refine ⟨Real.Interval.project_outer P.dom.nominal f ⟨y, hy.1, rfl⟩, ?_⟩
  show ∀ i, (P.op i).IsMetWithin ((P.nominalCore.reindexVars f).eval (fun k => y (f k)) i)
    |toReal (P.b_error i)|
  rw [Real.PolyLevelSet.eval_reindexVars P.nominalCore hf h0]
  exact hy.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
