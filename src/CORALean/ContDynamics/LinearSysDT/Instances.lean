module

public import CORALean.ContDynamics.Reach.Reach
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachUnionOuter

@[expose] public section

/-!
# `LinearSysDT` instantiates `Reach`

`params` is `Reach.InputParams` counted in sampling periods, `U` among them as in
CORA, the combined input `B U ⊕ c ⊕ E W` of the canonical form in state coordinates, which
`Trajectory.canonical` reads every run of the full equation into; `options` is
`LinearSysDT.ReachOptions`. `reachExact` is `reachUnionExact`
over `tFinal - tStart` steps, the system being time-invariant, `reach` is
`reachUnion` (always `some`: nothing here can fail at run time), and the guarantee
is `reachUnion_outer` — nothing new, every field already proved for its own
sake in `Definitions`, `Operations` and `Theorems`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ========================================  INSTANCES  ========================================= --

instance LinearSysDT.reachInstance :
    Reach (LinearSysDT 𝕋) (fun n => Reach.InputParams (S n) (S n) ℕ)
      LinearSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact params.X₀ params.U (params.tFinal - params.tStart)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options _ h := by
    -- the one set returned is `reachUnion`'s
    cases h
    exact sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
