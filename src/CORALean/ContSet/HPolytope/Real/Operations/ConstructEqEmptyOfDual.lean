import CORALean.ContSet.HPolytope.Real.Operations.ConstructEqFeasible
import CORALean.Global.LinProg.API

/-!
# `HPolytope.construct_eq_empty_of_dual`

Weights that cancel the objective but not the right-hand side prove the
description denotes nothing — the certificate of infeasibility an LP solver
returns instead of a solution.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

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
