import CORALean.ContDynamics.LinearSys.ManualReach

/-!
# `manualRun` reaches `t_k = k·Δt`

The arithmetic half of what [1, Alg. 1]'s `Ensure` clause presupposes: that the loop of
lines 4-11, run `K = t_end/Δt` times, reaches `t_end` exactly — needed to read `manualReach`'s
`K` as the paper's own `t_end/Δt` rather than an unrelated bound.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Line 5's recursion, unfolded: the state `manualRun` reaches after `k` steps sits at
`t_k = k·Δt`. -/
theorem LinearSys.manualRun_t_eq (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n)) (Δt : ℝ)
    (η ρ k : ℕ) : (sys.manualRun X₀ U Δt η ρ k).t = k * Δt := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSys.manualRun, LinearSys.manualInit]
  | succ k ih =>
    simp only [LinearSys.manualRun, LinearSys.manualStep]
    push_cast
    rw [ih]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
