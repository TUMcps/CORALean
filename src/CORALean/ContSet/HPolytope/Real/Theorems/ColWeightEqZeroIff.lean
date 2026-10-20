module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `HPolytope.colWeight` is zero exactly when no row reads the direction

A sum of absolute values vanishes exactly when every term does.

## Inputs
* `P` – H-polytope
* `v` – point

## Hypotheses
* none

## Conclusion
* no row reads `v` exactly when the rows' weight along `v` is zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- No row reads `v` exactly when the rows' weight along `v` is zero. -/
theorem HPolytope.colWeight_eq_zero_iff (P : HPolytope α) (v : α) :
    P.colWeight v = 0 ↔ (∀ i, P.A i v = 0) ∧ ∀ i, P.Ae i v = 0 := by -- --- PROOF ---
  have h1 : 0 ≤ ∑ i, |P.A i v| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h2 : 0 ≤ ∑ i, |P.Ae i v| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [HPolytope.colWeight, add_eq_zero_iff_of_nonneg h1 h2,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
