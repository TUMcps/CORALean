module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExponentialRemainder
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubExpTaylorMemExpRemainderInterval
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The Taylor remainder of the exponential of every member lies in `exponentialRemainder`

[1, Eq. 6] at one matrix gives `|e^M - Σ_{i ≤ η} Mⁱ/i!| ≤ e^{|M|} - Σ_{i ≤ η} |M|ⁱ/i!` entrywise.
A member `M` of the box is dominated by `N = abs(intMat)` entrywise, so `|M|ⁱ ≤ Nⁱ` for every
power (`aux_pow_entry_le_pow_entry`) and the series tail at `|M|` is under the tail at `N`, term by
term.

## Inputs
* `A` – interval matrix
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hM` – member lies in the interval matrix

## Conclusion
* the member's Taylor remainder lies in the remainder enclosure

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `0 ≤ B ≤ C` entrywise gives `0 ≤ Bᵏ ≤ Cᵏ` entrywise. -/
private theorem MatExp.aux_pow_entry_le_pow_entry {B C : Mat ℝ n n} (hB : ∀ i j, 0 ≤ B i j)
    (h : ∀ i j, B i j ≤ C i j) (k : ℕ) (i j : Fin n) : -- --- CONCL ---
    0 ≤ (B ^ k) i j ∧ (B ^ k) i j ≤ (C ^ k) i j := by -- --- PROOF ---
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    exact ⟨Finset.sum_nonneg fun l _ => mul_nonneg (ih i l).1 (hB l j),
      Finset.sum_le_sum fun l _ =>
        mul_le_mul (ih i l).2 (h l j) (hB l j) ((ih i l).1.trans (ih i l).2)⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Taylor remainder of `e^M` of every `M` in the box lies in `exponentialRemainder`. -/
theorem MatExp.exponentialRemainder_outer (A : Interval (Mat ℝ n n)) (η : ℕ) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) : -- --- CONCL ---
    exp M - MatExp.expTaylor M η ∈
      (MatExp.exponentialRemainder A η).construct := by -- --- PROOF ---
  -- the bound matrix `N = abs(intMat)` is nonnegative and equals its own absolute value
  set N := A.absMax with hN
  have hN0 : ∀ i j, 0 ≤ N i j := fun i j => le_max_of_le_left (abs_nonneg _)
  have hNabs : MatExp.absMat N = N := funext fun i => funext fun j => abs_of_nonneg (hN0 i j)
  have hMN : ∀ i j, MatExp.absMat M i j ≤ N i j := fun i j => by
    have h := Interval.mem_mat_iff.mp hM i j
    show |M i j| ≤ max |A.inf i j| |A.sup i j|
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (A.inf i j), le_max_left |A.inf i j| |A.sup i j|, h.1],
      h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  -- the remainder of `M` is entrywise under that of its absolute value ...
  have h1 := MatExp.exp_sub_expTaylor_mem_expRemainderInterval M zero_le_one η j k
  rw [one_smul] at h1
  -- ... which is under that of `N`, series term by series term
  have hsM := MatExp.hasSum_expRemainderMat_entry M 1 η j k
  have hsN := MatExp.hasSum_expRemainderMat_entry N 1 η j k
  rw [hNabs] at hsN
  have h2 : MatExp.expRemainderMat M 1 η j k ≤ MatExp.expRemainderMat N 1 η j k :=
    hasSum_le (fun i => by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (MatExp.aux_pow_entry_le_pow_entry (fun p q => abs_nonneg _) hMN _ j k).2) hsM hsN
  have hW : MatExp.expRemainderMat N 1 η j k = (exp N - MatExp.expTaylor N η) j k := by
    simp only [MatExp.expRemainderMat, hNabs, one_smul]
  rw [hW] at h2
  have h3 := abs_le.mp (h1.trans h2)
  show (0 - (exp N - MatExp.expTaylor N η)) j k ≤ (exp M - MatExp.expTaylor M η) j k ∧
    (exp M - MatExp.expTaylor M η) j k ≤ (0 + (exp N - MatExp.expTaylor N η)) j k
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
