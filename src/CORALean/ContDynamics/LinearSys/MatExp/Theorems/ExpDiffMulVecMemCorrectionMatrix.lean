module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix

@[expose] public section

/-!
# The variation of a point under the flow, as the interpolation plus the correction

`[1, Eq. 6]` writes `Δx(t) = x(t) - x(0) ⊆ (t/r)(e^{Ar} - I + F) x(0)` for `t ∈ [0, r]`, with
the correction matrix `F` of `[2]`. With the `F` of `[2, Prop. 3.1]` (`MatExp.correctionMatrix`)
what is proved is `Δx(t) = (t/r)(e^{Ar} - I) x(0) + F x(0)` for some `F` of the interval matrix:
`F` is not scaled by `t/r`, which `MatExp.expDiff_mem_correctionMatrix` does not give.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mulVec_mem_correctionMatrix (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (x : Vec ℝ n) : -- --- CONCL ---
    ∃ F ∈ (MatExp.correctionMatrix A r (m + 2)).construct,
      exp (t • A) *ᵥ x - x = (t / r) • ((exp (r • A) - 1) *ᵥ x) + F *ᵥ x := by -- --- PROOF ---
  refine ⟨_, MatExp.expDiff_mem_correctionMatrix A hr hε ht0 htr, ?_⟩
  simp only [sub_mulVec, smul_mulVec, one_mulVec]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
