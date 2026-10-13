import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.compactEqs`

The equality rows `compact_ 'zeros'` keeps: those that are not the row `0 = 0`, the all-zero
row of `[A b]`. Inequality rows are not touched, CORA's constraint being `A β = b` alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The equality rows that are not `0 = 0`. -/
noncomputable def ConZonotope.compactEqs {h : ℕ} (P : HPolytope (Vec ℝ h)) : Finset (Fin P.me) :=
  open Classical in
  Finset.univ.filter fun i => ¬(P.Ae i = 0 ∧ P.be i = 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
