module

public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Boundedness by the `n + 1` normals of a simplex

[1, Eq. 16]: a polyhedron is bounded exactly when its support function is finite along the
`n + 1` facet normals of a simplex, the rows of `[Iₙ -1]ᵀ`: `xᵢ ≤ aᵢ` for each coordinate and
`-∑ xᵢ ≤ a₀` bound every coordinate from both sides. Nothing about the polyhedron is used, so
this holds for every `P`, equality rows included.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isBounded_iff_supportFunc_simplex (P : HPolytope (Vec ℝ n)) :
    Bornology.IsBounded P.construct ↔
      (∀ i : Fin n, ∃ a : ℝ, supportFunc P.construct (LinearMap.proj i) ≤ (a : EReal)) ∧
        ∃ a : ℝ, supportFunc P.construct (-∑ i : Fin n, LinearMap.proj i) ≤ (a :
        EReal) := by -- --- PROOF ---
  simp only [supportFunc_le_coe_iff]
  constructor
  · intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    refine ⟨fun i => ⟨R, fun x hx => ?_⟩, ⟨n * R, fun x hx => ?_⟩⟩
    · exact le_trans (le_trans (le_abs_self _) (norm_le_pi_norm x i)) (hR x hx)
    -- `-∑ xᵢ ≤ ∑ |xᵢ| ≤ n R`
    · simp only [LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_proj,
        Function.eval]
      have hle : ∀ i, -x i ≤ R := fun i =>
        le_trans (le_trans (neg_le_abs _) (norm_le_pi_norm x i)) (hR x hx)
      calc -∑ i, x i = ∑ i, -x i := (Finset.sum_neg_distrib _).symm
        _ ≤ ∑ _i : Fin n, R := Finset.sum_le_sum fun i _ => hle i
        _ = n * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rintro ⟨ha, a₀, h₀⟩
    choose a ha using ha
    -- every coordinate lies within `|a₀| + 2 ∑ |aₖ|`
    refine isBounded_iff_forall_norm_le.mpr ⟨|a₀| + 2 * ∑ k, |a k|, fun x hx => ?_⟩
    have hsum : 0 ≤ ∑ k, |a k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hup : ∀ k, x k ≤ a k := fun k => ha k x hx
    have hlow : -∑ k, x k ≤ a₀ := by
      have := h₀ x hx
      simpa [LinearMap.coe_proj, Function.eval] using this
    -- `aᵢ - xᵢ ≤ ∑ (aₖ - xₖ)`, the terms being nonnegative
    have hgap : a i - x i ≤ ∑ k, (a k - x k) :=
      Finset.single_le_sum (f := fun k => a k - x k) (fun k _ => sub_nonneg.mpr (hup k))
        (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hgap
    have hai : |a i| ≤ ∑ k, |a k| :=
      Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    have hsa : ∑ k, a k ≤ ∑ k, |a k| := Finset.sum_le_sum fun k _ => le_abs_self _
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (a i), le_abs_self a₀]
    · linarith [hup i, le_abs_self (a i), abs_nonneg a₀]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
