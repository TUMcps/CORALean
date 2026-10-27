module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.OneParamPowEq
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

@[expose] public section

/-!
# A matrix polynomial in `C + βG`, by the powers of `β`

`Σ_{i=0}^η a_i (C + βG)ⁱ = Σ_{k=0}^η βᵏ u_k` with `u_0 = Σ_{i=0}^η a_i D_i` and
`u_k = Σ_{i=k}^η a_i F_i^{(k)}`: `MatExp.oneParam_pow_eq` term by term, the two sums exchanged.
At `a_i = rⁱ/i!` this is the step of the proof of [1, Thm. 1] defining `C̃_K` and `G̃_K^{(l)}`; at
`a_i = r^{i+1}/(i+1)!` it is the partial input solution's `Σ Aⁱ(β) r^{i+1}/(i+1)!` that
[1, Sec. IV-B] says "can be computed similarly".

## Inputs
* `C` – center matrix
* `G` – generator matrix
* `a` – series coefficients
* `β` – generator weight
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the matrix polynomial regroups by powers of the weight

## References

* [1] [M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". 2012 American Control Conference (ACC),
      2012.](../../../../../../references/2012/althoff-acc-low-order-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.oneParam_sum_pow_eq (C G : Mat ℝ n n) (a : ℕ → ℝ) (β : ℝ) (η : ℕ) : -- --- CONCL ---
    ∑ i ∈ Finset.range (η + 1), a i • (C + β • G) ^ i = ∑ k ∈ Finset.range (η + 1), β ^ k •
      (if k = 0 then ∑ i ∈ Finset.range (η + 1), a i • MatExp.oneParamD C i
      else ∑ i ∈ Finset.Icc k η, a i • MatExp.oneParamF C G i k) := by -- --- PROOF ---
  -- each term, split by the powers of `β`
  have hterm : ∀ i, a i • (C + β • G) ^ i = a i • MatExp.oneParamD C i +
      ∑ l ∈ Finset.Icc 1 i, β ^ l • (a i • MatExp.oneParamF C G i l) := fun i => by
    rw [MatExp.oneParam_pow_eq, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  simp only [hterm, Finset.sum_add_distrib]
  -- exchange the sums over `i ≤ η` and `1 ≤ l ≤ i`
  rw [Finset.sum_comm' (t' := Finset.Icc 1 η) (s' := fun l => Finset.Icc l η) (fun i l => by
    simp only [Finset.mem_range, Finset.mem_Icc]; omega)]
  conv_rhs => rw [Finset.sum_range_succ', if_pos rfl, pow_zero, one_smul, add_comm]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_neg (by omega), Finset.smul_sum, add_comm 1 k]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
