module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The normal equations give a least-squares fit

[1, Eq. 4]: `min_A Σᵢ ‖ẋ(tᵢ) - A φ(x(tᵢ), u(tᵢ))‖²`, the columns of `Ẋ` and `Φ` the data. If
`(Ẋ - A Φ) Φᵀ = 0`, every other `B` costs as much plus `‖(A - B) Φ‖²`: the residual is
orthogonal to every `M Φ`. Both closed forms the paper gives, (5) corrected and (6), are shown
optimal through this.

## Inputs
* `Xd` – derivative snapshots
* `Φ` – regressor snapshots
* `A` – candidate matrix
* `B` – competing matrix

## Hypotheses
* `hA` – the candidate solves the normal equations

## Conclusion
* the candidate's squared error is at most the competing matrix's

## References

* [1] [N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of Hybrid
      Automata from Noisy Data". Proceedings of the 28th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2025.](../../../references/2025/kochdumper-hscc-hybrid-automata-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n v N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 4]: a solution of the normal equations `(Ẋ - A Φ) Φᵀ = 0` minimizes the
least-squares cost. -/
theorem leastSquares_le_of_normal_eq (Xd : Mat ℝ n N) (Φ : Mat ℝ v N) (A : Mat ℝ n v)
    (hA : (Xd - A * Φ) * Φᵀ = 0) (B : Mat ℝ n v) : -- --- CONCL ---
    ∑ i, ∑ a, ((Xd - A * Φ) a i) ^ 2 ≤ ∑ i, ∑ a, ((Xd - B * Φ) a i) ^ 2 := by -- --- PROOF ---
  set E := Xd - A * Φ
  set F := (A - B) * Φ
  have hsplit : Xd - B * Φ = E + F := by simp only [E, F, Matrix.sub_mul]; abel
  -- the cross term `Σ E F` is `Σ (A - B) (E Φᵀ) = 0`
  have hcross : ∑ i, ∑ a, E a i * F a i = 0 := by
    have h : ∀ a j, (E * Φᵀ) a j = 0 := fun a j => by rw [hA]; rfl
    calc ∑ i, ∑ a, E a i * F a i
        = ∑ a, ∑ j, (A - B) a j * (E * Φᵀ) a j := by
          simp only [F, E, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by simp [h]
  rw [hsplit]
  have hexp : ∑ i, ∑ a, ((E + F) a i) ^ 2
      = ∑ i, ∑ a, (E a i) ^ 2 + 2 * ∑ i, ∑ a, E a i * F a i + ∑ i, ∑ a, (F a i) ^ 2 := by
    simp only [Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hexp, hcross, mul_zero, add_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    sq_nonneg _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
