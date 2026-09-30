import CORALean.ContDynamics.LinearSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinearSysDT.Definitions.WithInput
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `LinearSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `p.K` of `sys.sys.reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance. Computable wherever
`sys.sys.reach` is: no `reduce`, no new arithmetic, `List.map` over its steps.
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

/-- The steps `0` through `p.K` of `sys.sys.reach`, at the shared initial set
`X₀` and the paired input `sys.U`. -/
def LinearSysDT.WithInput.reachUnion (sys : LinearSysDT.WithInput 𝕋 S n)
    (p : LinearSysDT.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  ⟨(List.range (p.K + 1)).map (fun k => sys.sys.reach ⟨X₀, sys.U, 0, k⟩ ⟨p.o, p.ho⟩)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
