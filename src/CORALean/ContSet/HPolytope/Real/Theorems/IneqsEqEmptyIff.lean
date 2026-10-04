import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.Global.LinProg.Farkas
import Mathlib.Algebra.BigOperators.Option

/-!
# Emptiness of an H-polytope by Farkas' lemma

[1, Eq. 9]: `{A x ≤ b} = ∅` exactly when some `y ≥ 0` has `Aᵀ y = 0` and `bᵀ y < 0`. The paper
asks for the optimal value `y*` of `min bᵀ y` over that cone to be negative; the cone makes the
value `-∞` whenever it is not `0`, so "some feasible `y` with `bᵀ y < 0`" is what is meant. The
"only if" half is Farkas' lemma, `exists_dual_of_forall_le_fintype` on the homogenised system
`A x - t b ≤ 0`, `-t ≤ 0`, which forces `t ≤ 0` exactly when no `x / t` is a point.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_eq_empty_iff (A : Mat ℝ q n) (b : Vec ℝ q) :
    (HPolytope.ineqs A b).construct = ∅ ↔
      ∃ y : Vec ℝ q, 0 ≤ y ∧ Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 := by -- --- PROOF ---
  constructor
  · intro hE
    -- the homogenised rows `A x - t b ≤ 0` and `-t ≤ 0`
    let F : Option (Fin q) → (Vec ℝ n × ℝ →ₗ[ℝ] ℝ) := fun o => match o with
      | some i => (HPolytope.rowLin A i).comp (LinearMap.fst ℝ _ ℝ) - b i • LinearMap.snd ℝ _ ℝ
      | none => -LinearMap.snd ℝ _ ℝ
    have hne : ∃ z, ∀ o, F o z ≤ (0 : Option (Fin q) → ℝ) o :=
      ⟨0, fun o => by cases o <;> simp [F]⟩
    -- a positive `t` would make `x / t` a point of the empty polytope
    have hle : ∀ z, (∀ o, F o z ≤ (0 : Option (Fin q) → ℝ) o) →
        LinearMap.snd ℝ (Vec ℝ n) ℝ z ≤ 0 := by
      rintro ⟨x, t⟩ hz
      by_contra ht
      replace ht : 0 < t := not_le.mp ht
      have hmem : t⁻¹ • x ∈ (HPolytope.ineqs A b).construct := by
        rw [HPolytope.mem_ineqs_iff]
        intro i
        have hi := hz (some i)
        simp only [F, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.smul_apply, LinearMap.snd_apply, smul_eq_mul, Pi.zero_apply] at hi
        have hrow : HPolytope.rowLin A i x = (A *ᵥ x) i := rfl
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ ht]
        linarith
      rw [hE] at hmem
      exact hmem
    obtain ⟨y, hy0, hc, -⟩ :=
      exists_dual_of_forall_le_fintype F 0 (LinearMap.snd ℝ _ ℝ) 0 hne hle
    refine ⟨fun i => y (some i), fun i => hy0 _, ?_, ?_⟩
    -- at `(e_k, 0)`: the `k`-th column of `A` weighted by `y` sums to zero
    · funext k
      have h := congrArg (fun f : Vec ℝ n × ℝ →ₗ[ℝ] ℝ => f (Pi.single k 1, 0)) hc
      rw [Fintype.sum_option] at h
      simp only [LinearMap.snd_apply, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, F, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.neg_apply, smul_eq_mul] at h
      have hrow : ∀ i, HPolytope.rowLin A i (Pi.single k 1) = A i k := fun i => by
        show (A *ᵥ Pi.single k 1) i = A i k
        simp [Matrix.mulVec_single]
      simp only [hrow, mul_zero, sub_zero, neg_zero] at h
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
      rw [zero_add] at h
      exact (h.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)).symm
    -- at `(0, 1)`: `bᵀ y = -1 - y_none < 0`
    · have h := congrArg (fun f : Vec ℝ n × ℝ →ₗ[ℝ] ℝ => f (0, 1)) hc
      rw [Fintype.sum_option] at h
      simp only [LinearMap.snd_apply, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, F, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.neg_apply, smul_eq_mul, map_zero, mul_one,
        zero_sub, mul_neg] at h
      have hsum : b ⬝ᵥ (fun i => y (some i)) = ∑ i, y (some i) * b i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hsum]
      have hn := hy0 none
      rw [Finset.sum_neg_distrib] at h
      linarith
  · rintro ⟨y, hy, hA, hb⟩
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hrows := HPolytope.mem_ineqs_iff.mp hx
    -- `yᵀ A x = (Aᵀ y)ᵀ x = 0`, while `yᵀ A x ≤ yᵀ b < 0`
    have hzero : y ⬝ᵥ (A *ᵥ x) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, zero_dotProduct]
    have hle : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hy i)
    rw [dotProduct_comm] at hb
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
