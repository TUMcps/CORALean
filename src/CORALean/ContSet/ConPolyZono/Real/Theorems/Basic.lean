module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Project
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

@[expose] public section

/-!
# `ContSet/ConPolyZono/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ} {α : Type}


-- ===============================  `ConPolyZono.mtimes_eq_map`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConPolyZono.mtimes_eq_map (M : Mat ℝ m n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono.mtimes M cPZ = cPZ.map (Matrix.mulVecLin M) := rfl


-- ===============================  `ConPolyZono.project_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem ConPolyZono.project_exact (cPZ : ConPolyZono (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cPZ.construct = (cPZ.project dims).construct :=
  ConPolyZono.map_exact (LinearMap.funLeft ℝ ℝ dims) cPZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
