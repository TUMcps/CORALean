import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.Global.LinProg.API

/-!
# Where a halfspace description's own bounds come from

A halfspace description *is* an LP feasible set, so weak duality applies to it
directly: a nonnegative weighting of its own rows bounds whatever objective the
weighting assembles.

This is the only place a bound enters the polytope files. Everything else
composes bounds it already has, which is why a solver never has to be trusted —
it supplies `y` and `z`, and if they are wrong the certificate simply fails to
typecheck.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem HPolytope.construct_eq_feasible (P : HPolytope α) :
    P.construct = Feasible P.A P.b P.Ae P.be := rfl

/-- `hc` is dual feasibility, `c = yᵀA + zᵀAe`, stated pointwise because a
functional is determined by what it does. -/
def HPolytope.boundOfDual (P : HPolytope α) {c : α →ₗ[ℝ] ℝ}
    (y : Fin P.m → ℝ) (z : Fin P.me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ x : α, c x = (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x) :
    SupportBound P.construct c :=
  SupportBound.mono (P.construct_eq_feasible).subset (SupportBound.ofDual y z hy hc)

/-- Weights that cancel the objective but not the right-hand side prove the
description denotes nothing — the certificate of infeasibility an LP solver
returns instead of a solution. -/
theorem HPolytope.construct_eq_empty_of_dual (P : HPolytope α)
    (y : Fin P.m → ℝ) (z : Fin P.me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (h0 : ∀ x : α, (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x = 0)
    (hneg : (∑ i, y i * P.b i) + ∑ i, z i * P.be i < 0) :
    P.construct = ∅ := by
  rw [P.construct_eq_feasible]
  exact eq_empty_of_dual y z hy h0 hneg

end CORALean.Real
