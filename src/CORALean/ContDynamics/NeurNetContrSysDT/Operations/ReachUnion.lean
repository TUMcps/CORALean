import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachParams
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `NeurNetContrSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `p.K` of `reach`, one per branch of the `SetUnion` —
the `Reach.reach` field of the instance, computable wherever `reach` is.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The steps `0` through `p.K` of `sys.reach`, at the shared initial set
`X₀`. -/
def NeurNetContrSysDT.reachUnion (sys : NeurNetContrSysDT 𝕋 S n)
    (p : NeurNetContrSysDT.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  ⟨(List.range (p.K + 1)).map (fun k => sys.reach ⟨X₀, 0, k⟩ ⟨p.o, p.ho⟩)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
