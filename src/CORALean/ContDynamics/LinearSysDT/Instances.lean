module

public import CORALean.ContDynamics.Interfaces
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachUnionOuter

@[expose] public section

/-!
# `LinearSysDT` instantiates `ContDynamicsDT` and `Reach`

`params` is `Reach.InputParams` counted in sampling periods, `U` among them as in CORA, the
combined input `B U ⊕ c ⊕ E W` of the canonical form in state coordinates; `options` is
`LinearSysDT.ReachOptions`. `reachExact` is `reachUnionExact` over `tFinal - tStart` steps, the
system being time-invariant, `reach` is `reachUnion` (always `some`), and the guarantee is
`reachUnion_outer`, every field already proved in `Definitions`, `Operations` and `Theorems`.
`LinearSysDT` is a `ContDynamicsDT`: `m` inputs and `r` disturbances, a run an `IsTrajectory`
of the whole equation under any noise.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ========================================  INSTANCES  ========================================= --

instance LinearSysDT.reachInstance :
    Reach (LinearSysDT 𝕋) (fun n _ => Reach.InputParams (S n) (S n) ℕ)
      LinearSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact params.X₀ params.U (params.tFinal - params.tStart)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options _ h := by
    -- the one set returned is `reachUnion`'s
    cases h
    exact sys.reachUnion_outer params options

/-- CORA's `linearSysDT` as a `ContDynamicsDT`: `B u` the input, `E w` the disturbance. -/
instance LinearSysDT.contDynamicsDT {n : ℕ} : ContDynamicsDT (LinearSysDT 𝕋 n) n where
  nrOfInputs sys := sys.m
  nrOfDisturbances sys := sys.r
  IsTrajectory sys X₀ U W x u w :=
    ∃ v y, LinearSysDT.IsTrajectory (S := 𝒮) sys X₀ U W Set.univ x u w v y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
