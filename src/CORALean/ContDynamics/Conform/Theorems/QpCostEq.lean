module

public import CORALean.ContDynamics.Conform.Definitions.IntervalNorm
public import CORALean.ContDynamics.Conform.Plant
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# [1, Thm. 2]: the quadratic program's objective is the Frobenius-norm cost

`z^T H z` with `H` from (24)-(26) is `∑_{k=0}^K ω_k ‖R(t_k) - ỹ(t_k)‖²_{F,P}`
(23): `trace(G(t_k)^T P G(t_k)) = ∑ⱼ αⱼ² gⱼ^T P gⱼ` (35), the stretch factors
squared against the diagonal of the template's Gram matrix, one block per template.
The program minimizes `½ z^T H z`, half the cost, with the same minimizers; its
constraints are [1, Thm. 1]'s, so a feasible point is conformant by `conformant_iff_lp`.
No sign condition on `α` and no definiteness of `P` is needed for the identity.

## Inputs
* `sys` – plant
* `ιX` – index type of the initial generators
* `ιW` – index type of the disturbance generators
* `ιV` – index type of the noise generators
* `GX` – initial template generators
* `αX` – initial stretch factors
* `GW` – disturbance template generators
* `αW` – disturbance stretch factors
* `GV` – noise template generators
* `αV` – noise stretch factors
* `P` – norm weight matrix
* `ω` – step weights
* `K` – horizon

## Hypotheses
* none

## Conclusion
* the weighted Frobenius cost is quadratic in the stretch factors

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". Proceedings of 10th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH23),
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- (35): the stretch comes out of the trace squared. -/
theorem aux_frobNormSq_smul {m : ℕ} {ι : Type} [Fintype ι] (P : Mat ℝ m m) (G : ι → Vec ℝ m)
    (α : ι → ℝ) :
    Conform.frobNormSq P (fun j => α j • G j)
      = ∑ j, (G j ⬝ᵥ (P *ᵥ G j)) * α j ^ 2 := by
  unfold Conform.frobNormSq
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- One step's `trace(G(t_k)^T P G(t_k))`, split into the blocks of (25). -/
theorem aux_step_frob (sys : Conform.Plant n p q) {ιX ιW ιV : Type} [Fintype ιX]
    [Fintype ιW] [Fintype ιV] (GX : ιX → Vec ℝ n) (αX : ιX → ℝ) (GW : ιW → Vec ℝ n)
    (αW : ιW → ℝ) (GV : ιV → Vec ℝ q) (αV : ιV → ℝ) (P : Mat ℝ q q) (k : ℕ) : -- --- CONCL ---
    Conform.frobNormSq P (fun j => Sum.elim (Sum.elim αX fun r : Fin k × ιW => αW r.2) αV j
        • Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
          (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j)
      = ∑ x, (((sys.C * sys.A ^ k) *ᵥ GX x) ⬝ᵥ (P *ᵥ ((sys.C * sys.A ^ k) *ᵥ GX x))) * αX x ^ 2
        + ∑ r, (∑ i : Fin k, ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)
            ⬝ᵥ (P *ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r))) * αW r ^ 2
        + ∑ l, (GV l ⬝ᵥ (P *ᵥ GV l)) * αV l ^ 2 := by -- --- PROOF ---
  rw [aux_frobNormSq_smul]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin k))]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `z^T H z` is `∑_{k ≤ K} ω_k ‖R(t_k) - ỹ(t_k)‖²_{F,P}`. -/
theorem Conform.Plant.qpCost_eq (sys : Conform.Plant n p q) {ιX ιW ιV : Type} [Fintype ιX]
    [Fintype ιW] [Fintype ιV] (GX : ιX → Vec ℝ n) (αX : ιX → ℝ) (GW : ιW → Vec ℝ n)
    (αW : ιW → ℝ) (GV : ιV → Vec ℝ q) (αV : ιV → ℝ) (P : Mat ℝ q q) (ω : ℕ → ℝ)
    (K : ℕ) : -- --- CONCL ---
    ∑ k ∈ Finset.range (K + 1), ω k * Conform.frobNormSq P (fun j =>
        Sum.elim (Sum.elim αX fun r : Fin k × ιW => αW r.2) αV j
        • Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
          (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j)
      = ∑ x, (∑ k ∈ Finset.range (K + 1), ω k * (((sys.C * sys.A ^ k) *ᵥ GX x)
            ⬝ᵥ (P *ᵥ ((sys.C * sys.A ^ k) *ᵥ GX x)))) * αX x ^ 2
        + ∑ r, (∑ k ∈ Finset.range (K + 1), ω k * ∑ i : Fin k,
            ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r) ⬝ᵥ (P *ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)))
            * αW r ^ 2
        + ∑ l, (∑ k ∈ Finset.range (K + 1), ω k * (GV l ⬝ᵥ (P *ᵥ GV l)))
            * αV l ^ 2 := by -- --- PROOF ---
  simp only [aux_step_frob sys GX αX GW αW GV αV P, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  -- each block: exchange the sum over steps with the one over generators
  rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιX)),
    Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιW)),
    Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιV))]
  simp only [mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
