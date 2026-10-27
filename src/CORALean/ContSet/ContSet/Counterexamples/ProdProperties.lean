module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

/-!
# Two cells of `[1, Table 1 (×)]` are false

"D × B = D, B": the line `{x₂ = 0} ⊂ ℝ²` is degenerate, `{0} ⊂ ℝ` is bounded, and their product
is unbounded — degeneracy says nothing about boundedness. "D × NB = D, NB": `∅` is degenerate,
`ℝ` unbounded, and `∅ × ℝ = ∅` is bounded.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* both product boundedness claims fail for some sets

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem prod_properties_counterexample : -- --- CONCL ---
    (∃ (S₁ : Set (Vec ℝ 2)) (S₂ : Set (Vec ℝ 1)), interior S₁ = ∅ ∧ Bornology.IsBounded S₂ ∧
      ¬ Bornology.IsBounded (S₁ ×ˢ S₂)) ∧
    (∃ (S₁ : Set (Vec ℝ 1)) (S₂ : Set (Vec ℝ 1)), interior S₁ = ∅ ∧
      ¬ Bornology.IsBounded S₂ ∧ Bornology.IsBounded (S₁ ×ˢ S₂)) := by -- --- PROOF ---
  refine ⟨⟨LinearMap.ker (LinearMap.proj 1 : Vec ℝ 2 →ₗ[ℝ] ℝ), {0}, ?_,
    Bornology.isBounded_singleton, fun hb => ?_⟩,
    ⟨∅, Set.univ, interior_empty, NormedSpace.unbounded_univ ℝ _, ?_⟩⟩
  -- the line is a proper subspace: `e₂` is not on it
  · by_contra hne
    have htop := Submodule.eq_top_of_nonempty_interior' _
      (Set.nonempty_iff_ne_empty.mpr hne)
    have hmem : (Pi.single 1 1 : Vec ℝ 2) ∈ LinearMap.ker (LinearMap.proj 1 : Vec ℝ 2 →ₗ[ℝ] ℝ) := by
      rw [htop]
      exact Submodule.mem_top
    simp at hmem
  -- `(t, 0)` runs off along the line
  · have hS := hb.fst_of_prod (Set.singleton_nonempty (0 : Vec ℝ 1))
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS
    have hmem : (R + 1) • (Pi.single 0 1 : Vec ℝ 2) ∈
        (LinearMap.ker (LinearMap.proj 1 : Vec ℝ 2 →ₗ[ℝ] ℝ) : Set (Vec ℝ 2)) := by simp
    have h := le_trans (norm_le_pi_norm ((R + 1) • (Pi.single 0 1 : Vec ℝ 2)) 0) (hR _ hmem)
    simp at h
    linarith [abs_nonneg (R + 1), le_abs_self (R + 1)]
  · rw [Set.empty_prod]
    exact Bornology.isBounded_empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
