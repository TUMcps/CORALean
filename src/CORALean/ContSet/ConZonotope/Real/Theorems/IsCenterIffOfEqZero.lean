module

public import CORALean.ContSet.ConZonotope.Real.Operations.IsCenter

@[expose] public section

/-!
# With no constraint rows the center is `c`

`isempty(cZ.A)` is CORA's first branch of `center`: the center is the stored `c`, and nothing else
is a center, the other branches needing a constraint row.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isCenter_iff_of_eq_zero {c : α} {G : Fin h → α} {A : Mat ℝ 0 h}
    {b : Vec ℝ 0} {x : α} : ConZonotope.IsCenter c G A b x ↔ x = c := by
  unfold ConZonotope.IsCenter
  simp


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
