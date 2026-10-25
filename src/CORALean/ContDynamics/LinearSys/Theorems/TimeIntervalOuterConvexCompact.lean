module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# The step enclosure at any convex, compact representation

`timeInterval_outer_inputSolution` with its six topological hypotheses read off
the representation, exactly as `ReachOuterConvexCompact` does at the sample
times.

`0 ∈ U` stays a hypothesis: it is a fact about where the input set sits, not about its shape, so no
class can supply it. With it the step is [1, Alg. 1]'s first window, `R̂([0, r]) + R̄([0, r])`, one
enclosure for the whole step; an input set off the origin is split instead, which needs a
representation that can recenter itself.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `r` – step length
* `m` – Taylor order offset
* `t` – time

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hr` – step length positive
* `hT` – step lies in the time domain
* `hε` – scaled norm small enough for the Taylor order
* `ht0` – time nonnegative
* `htr` – time within the step
* `h0` – origin in the input set

## Conclusion
* the trajectory's state at the time lies in the step enclosure

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every trajectory whose input set is convex, compact and contains the origin
stays in the step enclosure at every time of the step, not only at its end. -/
theorem LinearSys.IsCanonicalTrajectory.timeInterval_outer_convexCompact
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus
      (sys.timeInterval r (m + 2) R₀) (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer_inputSolution hr hT hε ht0 htr
    (ConvexSet.convex_construct U) (CompactSet.isClosed_construct U)
    (CompactSet.isBounded_construct U)
    (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
    (CompactSet.isBounded_construct _) h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
