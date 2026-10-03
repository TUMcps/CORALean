import CORALean.ContSet.PolyZonotope.Real.Operations.IsFullDimCora
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Full dimension implies CORA's rank test

The set lies in the translate by `c` of the span of the generators of both blocks, and a
proper subspace has no interior (`Submodule.eq_top_of_nonempty_interior'`). So a polynomial
zonotope with an interior point passes `rank([G GI]) == n`: the test is necessary. The converse
fails (`isFullDim_cora_counterexample`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isFullDimCora_of_interior (pZ : PolyZonotope α)
    (h : (interior pZ.construct).Nonempty) : pZ.isFullDimCora := by -- --- PROOF ---
  set W := Submodule.span ℝ (Set.range pZ.G ∪ Set.range pZ.GI) with hW
  -- the set lies in a translate of `W`
  have hsub : pZ.construct ⊆ (fun v => pZ.c + v) '' (W : Set α) := by
    rintro x ⟨a, β, -, -, rfl⟩
    refine ⟨_, ?_, by rw [add_assoc]⟩
    refine W.add_mem (W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (W.sum_mem fun j _ => W.smul_mem _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  obtain ⟨y, hy⟩ := h
  have h1 := interior_mono hsub hy
  have h1' : y ∈ (Homeomorph.addLeft pZ.c) '' interior (W : Set α) := by
    rw [Homeomorph.image_interior]; exact h1
  have h2 : (interior (W : Set α)).Nonempty := by
    obtain ⟨v, hv, -⟩ := h1'
    exact ⟨v, hv⟩
  -- a subspace with an interior point is the whole space
  have htop : W = ⊤ := Submodule.eq_top_of_nonempty_interior' _ h2
  unfold PolyZonotope.isFullDimCora
  rw [← hW, htop, finrank_top]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
