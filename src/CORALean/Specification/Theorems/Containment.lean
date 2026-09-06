import CORALean.Specification.Specification
import CORALean.Global.LinProg.LinProg

/-!
# Bounds certify that a safe set is stayed inside

A safe set given by halfspaces is checked one halfspace at a time, and each is a
bound in that halfspace's own direction — the same object `Global.LinProg`
returns, so nothing new is needed to discharge the check.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O : Set α}

/-- A safe set cut out by directions, checked in each of them. -/
theorem aux_subset_halfspaces {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    O ⊆ {x | ∀ i, c i x ≤ d i} :=
  fun _ hx i => le_trans ((u i).le _ hx) (h i)

theorem Specification.holds_safeSet_of_bounds {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    (Specification.safeSet {x | ∀ i, c i x ≤ d i}).Holds O :=
  aux_subset_halfspaces c d u h

end CORALean.Real
