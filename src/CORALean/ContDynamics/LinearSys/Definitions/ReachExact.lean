module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The exact set `Reach LinearSys` is asked to enclose

Every image of a bare initial set under the homogeneous flow, at every time
of `[0, tFinal]` — [1, Def. 3.1] at `U = 0`, the case `Reach.reachExact` has
room for. `reach_outer` and `reachWrappingFree_outer` put it inside `reach` and
`reachWrappingFree`, one window at a time.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every image of a bare initial set `X₀` under `exp (t • sys.A)`, at every
`t ∈ [0, tFinal]`. -/
noncomputable def LinearSys.reachExact (sys : LinearSys 𝕋 n) (tFinal : ℝ)
    (X₀ : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ t ∈ Set.Icc 0 tFinal, ∃ x₀ ∈ X₀, x = exp (t • toRealMat sys.A) *ᵥ x₀}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
