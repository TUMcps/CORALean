import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachParams
import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `NeurNetContrSys.reach`, packaged as `Reach`'s `SetUnion`

The periods `0` through `p.H` of `reach`, at `reachOrder`'s own Taylor order,
one per branch of the `SetUnion` — the `Reach.reach` field of the instance.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The periods `0` through `p.H` of `sys.reach`, at `reachOrder`'s own order
and the shared initial set `X₀`. -/
noncomputable def NeurNetContrSys.reachUnion (sys : NeurNetContrSys 𝕋 S n)
    (p : NeurNetContrSys.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  ⟨(List.range (p.H + 1)).map (fun i =>
    sys.reach p.o (sys.reachOrder p.Δt) p.N p.ho p.Δt X₀ i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
