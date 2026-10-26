module

public import CORALean.Specification.Specification
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# Bounds certify that a safe set is stayed inside

A safe set given by halfspaces is checked one halfspace at a time, and each is a
bound in that halfspace's own direction — the same object `Global.SupportFunction`
returns, so nothing new is needed to discharge the check.

## Inputs
* `ι` – index type of the directions
* `c` – directions
* `d` – offsets
* `u` – support bounds of the set

## Hypotheses
* `h` – each bound is at most its offset

## Conclusion
* the safe set specification holds of the set
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
private theorem aux_subset_halfspaces {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
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
