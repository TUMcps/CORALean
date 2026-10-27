module

public import CORALean.ContDynamics.Conform.Definitions.Glo

@[expose] public section

/-!
# One more factor of the Jacobian product

`∏_{l=1}^{m+1} A_{k+1-l} = A_k ∏_{l=1}^m A_{k-l}`: the product `prodJac` of the GLO matrices
of [1, Cor. 1] and [1, Cor. 2] grows by its latest factor on the left, which is what unrolling
a recursion `x_{k+1} = A_k x_k + …` needs.

## Inputs
* `A` – Jacobians per step
* `k` – step
* `m` – number of factors

## Hypotheses
* none

## Conclusion
* the product with one more factor is the latest Jacobian times the shorter product

## References

* [1] [L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control,
      2026.](../../../../../references/2026/luetzow-tac-reachset-conformant-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `∏_{l=1}^{m+1} A_{k+1-l} = A_k ∏_{l=1}^m A_{k-l}`. -/
theorem Conform.prodJac_succ (A : ℕ → Mat ℝ n n) (k m : ℕ) : -- --- CONCL ---
    Conform.prodJac A (k + 1) (m + 1) = A k * Conform.prodJac A k m := by -- --- PROOF ---
  simp only [Conform.prodJac]
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply]
  congr 1
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
