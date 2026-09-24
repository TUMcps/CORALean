import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSys.Operations.ReachUnion
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `reachUnion` encloses `reachUnionExact`

`timeIntervalStep_outer` at `reachOrder_admissible`, for every member `A` and
every `t ∈ [0, p.r]` at once: the single branch of `reachUnion` is the same
set throughout, exactly `LinearSys.reachUnion_outer`'s argument.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachUnion_outer (sys : LinParamSys ℐ n) (p : LinParamSys.ReachParams)
    (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  rintro _ ⟨A, hA, t, ht, x₀, hx₀, rfl⟩
  refine SetUnion.mem_construct.mpr ⟨sys.timeIntervalStep p.r (sys.reachOrder p.r + 2) X₀,
    List.mem_singleton_self _, ?_⟩
  exact sys.timeIntervalStep_outer p.hr (sys.reachOrder_admissible p.r) X₀ hA ht.1 ht.2
    (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
