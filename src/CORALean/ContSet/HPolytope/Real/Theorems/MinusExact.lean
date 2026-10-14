module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact

@[expose] public section

/-!
# `HPolytope.minus` is exactly the shift by `-v`

Every point of the polytope less `v`, and no other point, satisfies the shifted
rows.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minus_exact (P : HPolytope α) (v : α) :
    (· - v) '' P.construct = (P.minus v).construct := by
  have h := HPolytope.translate_exact (-v) P
  simp only [sub_eq_add_neg, add_comm _ (-v)]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
