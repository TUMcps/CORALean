module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.ReindexVars
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `PolyLevelSet.reindexVars`'s rows

At an injective `f` that reaches every variable some monomial reads, the reindexed rows at
`y ∘ f` are `P`'s at `y`: a monomial is the same product, its factors outside the range of `f`
being at exponent zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reindexed rows at `y ∘ f` are `P`'s at `y`, where `f` is injective and every variable
outside its range is read by no monomial. -/
theorem PolyLevelSet.eval_reindexVars (P : PolyLevelSet n) {n' : ℕ} {f : Fin n' → Fin n}
    (hf : Function.Injective f) (h0 : ∀ k, k ∉ Set.range f → ∀ l, P.R k l = 0)
    (y : Vec ℝ n) :
    (P.reindexVars f).eval (fun k => y (f k)) = P.eval y := by -- --- PROOF ---
  have hμ : PolyZonotope.monomial (P.reindexVars f).R (fun k => y (f k))
      = PolyZonotope.monomial P.R y := by
    funext l
    show ∏ k, y (f k) ^ P.R (f k) l = ∏ k, y k ^ P.R k l
    rw [← Finset.prod_image (f := fun k => y k ^ P.R k l) (fun a _ b _ h => hf h)]
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    rw [h0 k (fun ⟨k', hk'⟩ => hk (Finset.mem_image.mpr ⟨k', Finset.mem_univ _, hk'⟩)) l,
      pow_zero]
  exact congrArg (fun v => P.A *ᵥ v - P.b) hμ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
