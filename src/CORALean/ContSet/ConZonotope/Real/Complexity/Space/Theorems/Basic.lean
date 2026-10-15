module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ContSet/ConZonotope/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {n : ℕ}


-- ==============================  `ConZonotope.intersection_P_m`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_m` count of `intersection`'s result. -/
theorem ConZonotope.intersection_P_m (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) :
    (cZ₁.intersection cZ₂).P.m = cZ₁.P.m + cZ₂.P.m := rfl


-- =============================  `ConZonotope.intersection_P_me`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_me` count of `intersection`'s result. -/
theorem ConZonotope.intersection_P_me (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) :
    (cZ₁.intersection cZ₂).P.me = cZ₁.P.me + cZ₂.P.me + n := rfl

end

section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `ConZonotope.linComb_P_m`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_m` count of `linComb`'s result. -/
theorem ConZonotope.linComb_P_m (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.linComb cZ₂).P.m = (cZ₁.h + cZ₁.h + cZ₁.P.m) + (cZ₂.h + cZ₂.h + cZ₂.P.m) := rfl


-- ================================  `ConZonotope.linComb_P_me`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_me` count of `linComb`'s result. -/
theorem ConZonotope.linComb_P_me (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.linComb cZ₂).P.me = cZ₁.P.me + cZ₂.P.me := by
  show 0 + cZ₁.P.me + (0 + cZ₂.P.me) = cZ₁.P.me + cZ₂.P.me
  omega


-- ==================================  `ConZonotope.plus_P_m`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `P_m` count of `plus`'s result. -/
theorem ConZonotope.plus_P_m (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.plus cZ₂).P.m = cZ₁.P.m + cZ₂.P.m := rfl


-- =================================  `ConZonotope.plus_P_me`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `P_me` count of `plus`'s result. -/
theorem ConZonotope.plus_P_me (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.plus cZ₂).P.me = cZ₁.P.me + cZ₂.P.me := rfl

end

section

open Matrix

variable {n m : ℕ}


-- =================================  `ConZonotope.mtimes_P_m`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_m` count of `mtimes`'s result. -/
theorem ConZonotope.mtimes_P_m (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M cZ).P.m = cZ.P.m := rfl


-- ================================  `ConZonotope.mtimes_P_me`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `P_me` count of `mtimes`'s result. -/
theorem ConZonotope.mtimes_P_me (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M cZ).P.me = cZ.P.me := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
