import CORALean.Specification.Specification
import CORALean.Global.LinProg.LinProg

/-!
# Bounds certify that a safe set is stayed inside

A safe set given by halfspaces is checked one halfspace at a time, and each is a
bound in that halfspace's own direction — the same object `Global.LinProg`
returns, so nothing new is needed to discharge the check.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O : Set α}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A safe set cut out by directions, checked in each of them. -/
theorem aux_subset_halfspaces {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    O ⊆ {x | ∀ i, c i x ≤ d i} :=
  fun _ hx i => le_trans ((u i).le _ hx) (h i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_safeSet_of_bounds {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    (Specification.safeSet {x | ∀ i, c i x ≤ d i}).Holds O :=
  aux_subset_halfspaces c d u h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
