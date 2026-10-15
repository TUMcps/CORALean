module

public import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ContSet/ZonoBundle/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =================================  `ZonoBundle.linComb_Z_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `Z_h` count of `linComb`'s result. -/
theorem ZonoBundle.linComb_Z_h (zB₁ zB₂ : ZonoBundle α) (p : Fin (zB₁.k * zB₂.k)) :
    ((zB₁.linComb zB₂).Z p).h =
      (zB₁.Z (finProdFinEquiv.symm p).1).h + (zB₂.Z (finProdFinEquiv.symm p).2).h + 1 := rfl


-- ==================================  `ZonoBundle.plus_Z_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `Z_h` count of `plus`'s result. -/
theorem ZonoBundle.plus_Z_h (zB₁ zB₂ : ZonoBundle α) (p : Fin (zB₁.k * zB₂.k)) :
    ((zB₁.plus zB₂).Z p).h =
      (zB₁.Z (finProdFinEquiv.symm p).1).h + (zB₂.Z (finProdFinEquiv.symm p).2).h := rfl

end

section

open Matrix

variable {n m : ℕ}


-- =================================  `ZonoBundle.mtimes_Z_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `Z_h` count of `mtimes`'s result. -/
theorem ZonoBundle.mtimes_Z_h (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    ((ZonoBundle.mtimes M zB).Z i).h = (zB.Z i).h := rfl


-- ============================  `ZonoBundle.mtimesMatZonotope_Z_h`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The `Z_h` count of `mtimesMatZonotope`'s result. -/
theorem ZonoBundle.mtimesMatZonotope_Z_h (M : Zonotope (Mat ℝ m n)) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) : ((ZonoBundle.mtimesMatZonotope M zB).Z i).h
      = M.h + (zB.Z i).h + M.h * (zB.Z i).h := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
