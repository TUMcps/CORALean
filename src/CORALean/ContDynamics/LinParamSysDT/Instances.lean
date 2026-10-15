module

public import CORALean.ContDynamics.Interfaces
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachUnionOuter

@[expose] public section

/-!
# `LinParamSysDT` instantiates `ContDynamicsDT` and `Reach`

`params` is `Reach.InputParams` counted in sampling periods, `U` among them as in
CORA; `options` is `LinParamSysDT.ReachOptions`. `reachExact` is `reachUnionExact`
over `tFinal - tStart` steps, the system being time-invariant, `reach` is
`reachUnion` (always `some`: nothing here can fail at run time), and the guarantee
is `reachUnion_outer`.

`LinParamSysDT` is a `ContDynamicsDT`: `m` inputs and no disturbance, a run a `IsTrajectory`, a
fresh `A k` and `B k` at every step, at some such matrices.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- ========================================  INSTANCES  ========================================= --

instance LinParamSysDT.reachInstance :
    Reach (LinParamSysDT 𝕄) (fun n _ => Reach.InputParams (S n) (S n) ℕ)
      LinParamSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact params.X₀ params.U (params.tFinal - params.tStart)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options _ h := by
    -- the one set returned is `reachUnion`'s
    cases h
    exact sys.reachUnion_outer params options

/-- CORA's `linParamSys` in discrete time as a `ContDynamicsDT`. -/
instance LinParamSysDT.contDynamicsDT {n : ℕ} : ContDynamicsDT (LinParamSysDT 𝕄 n) n where
  nrOfInputs sys := sys.m
  nrOfDisturbances _ := 0
  IsTrajectory sys X₀ U W x u w :=
    (∃ A B, LinParamSysDT.IsTrajectory (S := 𝒮) sys X₀ U x u A B) ∧
      ∀ k, w k ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
