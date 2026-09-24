import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinParamSysDT.Definitions.WithInput
import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `LinParamSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `p.K` of `sys.sys.reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance, computable wherever
`sys.sys.reach` is.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The steps `0` through `p.K` of `sys.sys.reach`, at the shared initial set
`X₀` and the paired input `sys.U`. -/
def LinParamSysDT.WithInput.reachUnion (sys : LinParamSysDT.WithInput 𝕄 S n)
    (p : LinParamSysDT.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  ⟨(List.range (p.K + 1)).map (fun k => sys.sys.reach p.o p.ho X₀ sys.U k)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
