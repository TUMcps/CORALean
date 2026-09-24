import CORALean.ContDynamics.LinearSys.Definitions.ReachParams

/-!
# The exact set `Reach LinearSys` is asked to enclose

Every image of a bare initial set under the homogeneous flow, at every time
of `[0, p.r]` — [1, Def. 3.1] at `U = 0`, the case `Reach.reachExact` has room
for. `reachUnion_outer` is `timeIntervalStep_outer` at every such time.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every image of a bare initial set `X` under `exp (t • sys.A)`, at every
`t ∈ [0, p.r]`. -/
noncomputable def LinearSys.reachUnionExact (sys : LinearSys 𝕋 n) (p : LinearSys.ReachParams)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) p.r, ∃ x₀ ∈ X, x = exp (t • toRealMat sys.A) *ᵥ x₀}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
