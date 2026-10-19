module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.ReindexVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalReindexVars

@[expose] public section

/-!
# A point of `PolyLevelSet.reindexVars`, over a floating-point scalar

At an injective `f` that reaches every variable some monomial reads, `y ∘ f` meets the reindexed
rows within their slacks exactly when `y` meets `P`'s: the read-back rows are the exact layer's
reindexed rows (`Real.PolyLevelSet.eval_reindexVars`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `y ∘ f` is in the reindexed set exactly when `y` is in `P`. -/
theorem PolyLevelSet.mem_reindexVars_iff (P : PolyLevelSet 𝕋 n) {n' : ℕ} {f : Fin n' → Fin n}
    (hf : Function.Injective f) (h0 : ∀ k, k ∉ Set.range f → ∀ l, P.R k l = 0)
    (y : Vec ℝ n) :
    (fun k => y (f k)) ∈ (P.reindexVars f).construct ↔ y ∈ P.construct := by
  show (∀ i, (P.op i).IsMetWithin ((P.nominalCore.reindexVars f).eval (fun k => y (f k)) i)
    |toReal (P.b_error i)|) ↔ _
  rw [Real.PolyLevelSet.eval_reindexVars P.nominalCore hf h0]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
