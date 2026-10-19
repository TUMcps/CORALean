module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ContSet/ConPolyZono/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {n : ℕ}


-- ===============================  `ConPolyZono.intersection_h`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `intersection`'s result. -/
theorem ConPolyZono.intersection_h (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.intersection cPZ₁ cPZ₂).h = (cPZ₁.h + cPZ₁.qI) + (cPZ₂.h + cPZ₂.qI) := rfl


-- ===============================  `ConPolyZono.intersection_m`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `m` count of `intersection`'s result. -/
theorem ConPolyZono.intersection_m (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.intersection cPZ₁ cPZ₂).cons.m = cPZ₁.cons.m + cPZ₂.cons.m + n := rfl


-- ===============================  `ConPolyZono.intersection_q`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `intersection`'s result. -/
theorem ConPolyZono.intersection_q (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.intersection cPZ₁ cPZ₂).cons.q
      = cPZ₁.cons.q + cPZ₂.cons.q + ((cPZ₁.h + cPZ₁.qI) + (cPZ₂.h + cPZ₂.qI)) := rfl


-- ==============================  `ConPolyZono.intersection_qI`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `qI` count of `intersection`'s result. -/
theorem ConPolyZono.intersection_qI (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.intersection cPZ₁ cPZ₂).qI = 0 := rfl

end

section

open Matrix

variable {k n : ℕ}


-- ==================================  `ConPolyZono.mtimes_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `mtimes`'s result. -/
theorem ConPolyZono.mtimes_h (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).h = cPZ.h := rfl


-- ==================================  `ConPolyZono.mtimes_m`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `m` count of `mtimes`'s result. -/
theorem ConPolyZono.mtimes_m (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).cons.m = cPZ.cons.m := rfl


-- ==================================  `ConPolyZono.mtimes_q`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `mtimes`'s result. -/
theorem ConPolyZono.mtimes_q (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).cons.q = cPZ.cons.q := rfl


-- =================================  `ConPolyZono.mtimes_qI`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `qI` count of `mtimes`'s result. -/
theorem ConPolyZono.mtimes_qI (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).qI = cPZ.qI := rfl

end

section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===================================  `ConPolyZono.plus_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `h` count of `plus`'s result. -/
theorem ConPolyZono.plus_h (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).h = cPZ₁.h + cPZ₂.h := rfl


-- ===================================  `ConPolyZono.plus_m`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `m` count of `plus`'s result. -/
theorem ConPolyZono.plus_m (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).cons.m = cPZ₁.cons.m
    + cPZ₂.cons.m := rfl


-- ===================================  `ConPolyZono.plus_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)

omit [Module ℝ α] in
/-- The `q` count of `plus`'s result. -/
theorem ConPolyZono.plus_q (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).cons.q = cPZ₁.cons.q
    + cPZ₂.cons.q := rfl


-- ==================================  `ConPolyZono.plus_qI`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `qI` count of `plus`'s result. -/
theorem ConPolyZono.plus_qI (cPZ₁ cPZ₂ : ConPolyZono α) :
    (cPZ₁.plus cPZ₂).qI = cPZ₁.qI + cPZ₂.qI := rfl

end

section

variable {n k : ℕ}


-- =================================  `ConPolyZono.quadMap_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `h` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_h (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).h = (cPZ.h + cPZ.qI + 1) * (cPZ.h + cPZ.qI + 1) := rfl


-- =================================  `ConPolyZono.quadMap_m`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `m` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_m (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).cons.m = cPZ.cons.m := rfl


-- =================================  `ConPolyZono.quadMap_q`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- The `q` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_q (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).cons.q = cPZ.cons.q := rfl


-- =================================  `ConPolyZono.quadMap_qI`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `qI` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_qI (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).qI = 0 := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
