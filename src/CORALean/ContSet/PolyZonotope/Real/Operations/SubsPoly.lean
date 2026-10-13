import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.subsPoly`

Output `ii` of `pZin` as a sum of monomials: CORA's `Gin0 = [cin, Gin]` with `eMin0 = [0, eMin]`,
the centre being the term with exponent `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Output `ii` of `pZin` as a sum of monomials. -/
noncomputable def PolyZonotope.subsPoly {nu : ℕ} (pZin : PolyZonotope (Vec ℝ nu)) (ii : Fin nu) :
    List (ℝ × (Fin pZin.p → ℕ)) :=
  (pZin.c ii, 0) :: (List.finRange pZin.h).map fun j => (pZin.G j ii, fun k => pZin.E k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
