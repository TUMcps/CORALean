import CORALean.ContDynamics.LinearSys.ReachSet
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution

/-!
# One computed set encloses the whole reachable set over a step

`timeInterval_outer_inputSolution` restated on `reachSet`, and the form the
two-step split is for: no trajectory, no input signal and no index appears
anywhere in it. The reachable set at every time of the step lies in
`timeIntervalStep ⊞ inputSolution`, and what is left are properties of `U`,
which a representation answers for.

That is what `reachSet` buys over the sampled statements: between `kΔt` and
`(k+1)Δt` this still speaks, where `reachSet_subset_reach` does not.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to enclose a whole step at once; for `reachSet_subset_reach`
where the input enclosure is supplied rather than computed. -/
theorem LinearSys.reachSet_subset_timeInterval_inputSolution (sys : LinearSys 𝕋 n)
    {T : Set ℝ} (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    sys.reachSet T R₀ U t ⊆ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) := by
  rintro _ ⟨x, u, traj, rfl⟩
  exact traj.timeInterval_outer_inputSolution hr hT hε ht0 htr hconv hclosed hbdd
    hRconv hRclosed hRbdd h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
