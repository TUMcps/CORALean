import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.coraWeight`

The share of a dependent generator that CORA's `@polyZonotope/zonotope` leaves free: half
if its exponent column is all even (a constant column included, which `zonotopeEven` frees
none of), all of it otherwise. The rest goes to the centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Half if the column is all even, all otherwise. -/
noncomputable def PolyZonotope.coraWeight {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : ℝ :=
  if ∀ k, E k i % 2 = 0 then 1 / 2 else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
