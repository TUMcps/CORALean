module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry

@[expose] public section

/-!
# `E(Δt, η)` grows with `Δt`

Entry by entry, for `0 ≤ t ≤ t_max`: `E(t, η) ≤ E(t_max, η)`. Each is the tail of the series
at `|A|t` past `η`, whose terms are nonnegative and increase with the time [1, Eq. 13]: what
lets `Ê(t_max)` stand for every `Ê(t)` of the interval.

## Inputs
* `A` – system matrix
* `t` – time
* `tmax` – larger time
* `η` – Taylor order
* `j` – row index
* `k` – column index

## Hypotheses
* `ht` – time nonnegative
* `htm` – time at most the larger time

## Conclusion
* the remainder entry grows with the time

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expRemainderMat_mono (A : Mat ℝ n n) {t tmax : ℝ} (ht : 0 ≤ t)
    (htm : t ≤ tmax) (η : ℕ) (j k : Fin n) :
    MatExp.expRemainderMat A t η j k ≤ MatExp.expRemainderMat A tmax η j k := by -- --- PROOF ---
  -- the tails, termwise: `t^i ≤ t_max^i` against the nonnegative entries of `|A|^i`
  refine hasSum_le (fun i => ?_) (MatExp.hasSum_expRemainderMat_entry A t η j k)
    (MatExp.hasSum_expRemainderMat_entry A tmax η j k)
  have hnn : 0 ≤ ((MatExp.absMat A) ^ (i + (η + 1))) j k :=
    (abs_nonneg _).trans (abs_pow_entry_le_absMat_pow_entry A _ j k)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ht htm _) (by positivity)) hnn

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
