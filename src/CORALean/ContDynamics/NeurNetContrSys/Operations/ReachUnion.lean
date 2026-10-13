import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `NeurNetContrSys.reach`, packaged as `Reach`'s `SetUnion`

The periods `0` through `H = tFinal - tStart` of `reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance. `η` is a floor,
raised to `reachOrder`'s order where that is higher, since only an order admissible
for `Δt` and the plant's matrix makes `reach_outer` hold.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The periods `0` through `tFinal - tStart` of `reach`, from `R0`, at `η`
raised to `reachOrder`'s order. -/
noncomputable def NeurNetContrSys.reachUnion (sys : NeurNetContrSys 𝕋 S n)
    (params : Reach.Params (S n) ℕ) (options : NeurNetContrSys.ReachOptions ℝ) : SetUnion (S n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let H := params.tFinal - params.tStart                           -- control periods
  let η := max options.η (sys.reachOrder Δt)             -- raised until admissible
  ⟨(List.range (H + 1)).map (fun i =>                               -- ⋃_{i ≤ H} R(iNΔt)
    sys.reach ⟨R₀, 0, i⟩ ⟨Δt, options.N, η, options.ρ, options.hZonotopeOrder⟩)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
