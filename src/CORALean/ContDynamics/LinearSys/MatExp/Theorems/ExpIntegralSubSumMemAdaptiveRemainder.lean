module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsParticularTailEntryLe
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The integrated exponential's tail lies in `Δt [-W, W]`

`∫₀^Δt e^{Aσ}dσ` minus its orders up to `η` is entrywise within `Δt |E(Δt, η)|`, so it is a
member of the interval matrix `adaptiveRemainder`: [1, Prop. 11]'s step (18), for
`errorSolution_adaptive`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegral_sub_sum_mem_adaptiveRemainder (A : Mat ℝ n n) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (η : ℕ) :
    (MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i)
      ∈ (MatExp.adaptiveRemainder A Δt η).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  -- the entry bound of the tail, and `E ≤ |E|`
  have hb := abs_le.mp (MatExp.abs_particularTail_entry_le A hΔt η j k)
  have hE : Δt * MatExp.expRemainderMat A Δt η j k
      ≤ Δt * |MatExp.expRemainderMat A Δt η j k| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hΔt
  have hE' : -(Δt * |MatExp.expRemainderMat A Δt η j k|)
      ≤ -(Δt * MatExp.expRemainderMat A Δt η j k) := neg_le_neg hE
  exact ⟨le_trans hE' hb.1, le_trans hb.2 hE⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
