import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`, `ẋ = A x + B u + c` with an output, reduced to `ẋ = A x + u`,
the input entering in state coordinates as in [1, Sec. 3.2]: `B U ⊕ c` is one
`mtimes` and one `plus` on the input set, so the folded form reaches the same states.

The output equation is `OutputEq`, paired with a computed set rather than stored
here: `discretize` hands `LinearSysDT` an input set of state contributions over a
step, so a `D` stored on either system would multiply the wrong set at one of them.

A trajectory on the time domain `T` (`Set.Ici 0`, `Set.Icc 0 τ`) is a Carathéodory
solution, stated by the integral equation [1, Def. 3.1] writes, not by a derivative
at every point: a zero-order-hold input has none at a jump (Sontag, *Math. Control
Theory*, Def. C.2.1). `meas` is the input's own regularity, restricted to `T`;
`cont` is Def. C.2.1's continuity, without which `intervalIntegral`'s junk value
would let `flow` admit an `x` nothing like a run. The derivative-everywhere
predicate is `ClassicalTrajectory`, and `ClassicalTrajectory.trajectory` puts each
of its runs among these, so a statement over `Trajectory` covers it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSys (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

/-- A Carathéodory run of `sys` on `T` from `R₀` with inputs in `U`: the flow
stated as the integral equation, so a run whose input jumps still is one. -/
structure LinearSys.Trajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
