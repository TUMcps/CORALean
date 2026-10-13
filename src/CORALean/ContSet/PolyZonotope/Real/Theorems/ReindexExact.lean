import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexPoint

/-!
# Reordering the dependent block loses nothing

`reindex` moves no data, so one factor vector reads both sides and the two
inclusions come out of a single equation, as they do for `compactGens`. That
equation is `reindex_point` with the independent block added back on either
side, the centre being `point`'s own first summand.

The `key` is stated with the *original* centre and independent block on both
sides. They are the reindexed ones up to unfolding, and writing them so keeps
the equation to the one sum that actually moves.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- so both inclusions hold at the very same coefficients
theorem PolyZonotope.reindex_exact (pZ : PolyZonotope α) (σ : Equiv.Perm (Fin pZ.h)) :
    pZ.construct = (pZ.reindex σ).construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ),
      pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, β j • pZ.GI j
        = pZ.c + (∑ i : Fin (pZ.reindex σ).h,
            PolyZonotope.monomial (pZ.reindex σ).E a i • (pZ.reindex σ).G i)
          + ∑ j, β j • pZ.GI j :=
    fun a β => congrArg (fun s => s + ∑ j, β j • pZ.GI j)
      (PolyZonotope.reindex_point pZ σ a).symm
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (key a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
