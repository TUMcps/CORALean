module

public import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `LinParamSys` instantiates `ContDynamics`, and at `ℐ` `Reach`

`params` is `Reach.InputParams` at real time: CORA's `params.U` in input coordinates. `options`
is `LinearSys.ReachStepOptions`. `reachExact` is `reachUnionExact` on `[0, tFinal - tStart]`,
the system being time-invariant, `reach` is `reachUnion`, `none` unless `0 < Δt`, and the
guarantee is `reachUnion_outer` [1, Alg. 1], constant-parameter, in `⌈(tFinal - tStart) / Δt⌉`
windows. The representation is asked to be convex and compact, what `inputSolution`'s enclosure
needs of `V = B U ⊕ c`. `LinParamSys` is a `ContDynamics`: `m` inputs, no disturbance, a run
an `IsTrajectory` (`'varParam'`, which every `'constParam'` run is too).

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinParamSys.reachInstance :
    Reach (LinParamSys ℐ) (fun n sys => Reach.InputParams (S n) (S sys.m) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params :=
    sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀) (construct params.U)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachUnion_outer params h

/-- CORA's `linParamSys` as a `ContDynamics`, its runs the time-varying-parameter ones. -/
instance LinParamSys.contDynamics {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
    {n : ℕ} : ContDynamics (LinParamSys 𝕄 n) n where
  nrOfInputs sys := sys.m
  nrOfDisturbances _ := 0
  IsTrajectory sys T X₀ U W x u w :=
    (∃ A B, LinParamSys.IsTrajectory (S := 𝒮) sys T X₀ U x u A B) ∧
      ∀ t ∈ T, w t ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
