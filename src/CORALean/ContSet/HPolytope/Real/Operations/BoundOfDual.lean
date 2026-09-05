import CORALean.ContSet.HPolytope.Real.Operations.ConstructEqFeasible
import CORALean.Global.LinProg.API

/-!
# `HPolytope.boundOfDual`

A halfspace description *is* an LP feasible set, so weak duality applies to it
directly: a nonnegative weighting of its own rows bounds whatever objective the
weighting assembles.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `hc` is dual feasibility, `c = yᵀA + zᵀAe`, stated pointwise because a
functional is determined by what it does. -/
def HPolytope.boundOfDual (P : HPolytope α) {c : α →ₗ[ℝ] ℝ}
    (y : Fin P.m → ℝ) (z : Fin P.me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ x : α, c x = (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x) :
    SupportBound P.construct c :=
  SupportBound.mono (P.construct_eq_feasible).subset (SupportBound.ofDual y z hy hc)

end CORALean.Real
