import CORALean.NN.Layers.Definitions.ApproxError
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The approximation errors are attained on a finite set of candidates

[1, Prop. 10]'s reduction: if `P ∩ [l,u]` is finite and nonempty and every point of `[l,u]` is
dominated, at a point of `P ∩ [l,u]`, by a point with a smaller `ϕ - p` and, in the other
direction, by one with a larger, then the approximation errors [1, Def. 6] are the minimum and
maximum of `ϕ - p` over `P ∩ [l,u]`: the `min_{x ∈ P ∩ [l,u]}` and `max_{x ∈ P ∩ [l,u]}` of the
proposition. No continuity is needed: the domination says where the extrema are.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxError_isExtreme (ϕ p : ℝ → ℝ) (P : Set ℝ) (l u : ℝ)
    (hfin : (P ∩ Set.Icc l u).Finite) (hne : (P ∩ Set.Icc l u).Nonempty)
    (hlo : ∀ x ∈ Set.Icc l u, ∃ q ∈ P ∩ Set.Icc l u, ϕ q - p q ≤ ϕ x - p x)
    (hup : ∀ x ∈ Set.Icc l u, ∃ q ∈ P ∩ Set.Icc l u, ϕ x - p x ≤ ϕ q - p q) :
    IsLeast ((fun x => ϕ x - p x) '' (P ∩ Set.Icc l u)) (approxErrorLow ϕ p l u) ∧
      IsGreatest ((fun x => ϕ x - p x) '' (P ∩ Set.Icc l u))
        (approxErrorUp ϕ p l u) := by -- --- PROOF ---
  set g : ℝ → ℝ := fun x => ϕ x - p x
  obtain ⟨a, haS, ha⟩ := Set.exists_min_image _ g hfin hne
  obtain ⟨b, hbS, hb⟩ := Set.exists_max_image _ g hfin hne
  -- the infimum and the supremum over `[l, u]` are the values at `a` and `b`
  have hmin : IsLeast (g '' Set.Icc l u) (g a) := by
    refine ⟨⟨a, haS.2, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hqS, hq⟩ := hlo x hx
    exact (ha q hqS).trans hq
  have hmax : IsGreatest (g '' Set.Icc l u) (g b) := by
    refine ⟨⟨b, hbS.2, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hqS, hq⟩ := hup x hx
    exact hq.trans (hb q hqS)
  refine ⟨?_, ?_⟩
  · rw [approxErrorLow, hmin.csInf_eq]
    exact ⟨⟨a, haS, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact ha x hx⟩
  · rw [approxErrorUp, hmax.csSup_eq]
    exact ⟨⟨b, hbS, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hb x hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
