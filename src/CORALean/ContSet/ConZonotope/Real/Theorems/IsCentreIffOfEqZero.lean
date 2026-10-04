import CORALean.ContSet.ConZonotope.Real.Operations.IsCentre

/-!
# With no constraint rows the centre is `c`

`isempty(cZ.A)` is CORA's first branch of `center`: the centre is the stored `c`, and nothing else
is a centre, the other branches needing a constraint row.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isCentre_iff_of_eq_zero {c : α} {G : Fin h → α} {A : Mat ℝ 0 h}
    {b : Vec ℝ 0} {x : α} : ConZonotope.IsCentre c G A b x ↔ x = c := by
  unfold ConZonotope.IsCentre
  simp


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
