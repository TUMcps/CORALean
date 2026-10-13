import CORALean.ContSet.ContSet.Operations.Minus

/-!
# `minus` encloses the translate
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Plus S α] [OfPoint S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `x - p` with `x` in `S` is in `minus S p`: `plus_outer`, the point `-p` being in
its singleton. -/
theorem ContSet.minus_outer (s : S) (p : α) :
    (fun x => x - p) '' construct s ⊆ construct (ContSet.minus s p) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Plus.plus_outer _ _ ⟨x, hx, -p, OfPoint.mem_ofPoint _, sub_eq_add_neg x p |>.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
