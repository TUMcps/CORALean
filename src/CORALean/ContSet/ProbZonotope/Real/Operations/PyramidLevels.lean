import CORALean.ContSet.ProbZonotope.Real.Operations.Max

/-!
# `ProbZonotope.pyramidLevels`

The array `maxVal` of CORA's `pyramid`: the density `max(probZ, mᵢ)` on the `mᵢ`-sigma bound for
each layer `i`, then the peak `max(probZ, 0)` as `maxVal(end+1)`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.pyramidLevels (P : ProbZonotope n) {k : ℕ} (mArray : Fin k → ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.snoc (fun i => P.max (mArray i)) (P.max 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
