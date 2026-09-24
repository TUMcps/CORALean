import CORALean.ContDynamics.LinearSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinearSys.Operations.ReachUnion
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `reachUnion` encloses `reachUnionExact`

`timeIntervalStep_outer` at `reachOrder_admissible`, for every `t ∈ [0, p.r]`
at once: the single branch of `reachUnion` is the same set at every one of
them, so no case split on `t` is needed to land in it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachUnion_outer (sys : LinearSys 𝕋 n) (p : LinearSys.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  rintro _ ⟨t, ht, x₀, hx₀, rfl⟩
  refine SetUnion.mem_construct.mpr ⟨sys.timeIntervalStep p.r (sys.reachOrder p.r + 2) X₀,
    List.mem_singleton_self _, ?_⟩
  exact sys.timeIntervalStep_outer p.hr (sys.reachOrder_admissible p.r) X₀ ht.1 ht.2
    (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
