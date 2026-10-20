module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

@[expose] public section

/-!
# `ContSet/PolyZonotope/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- ==================================  `PolyZonotope.bilin_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `h` count of `bilin`'s result. -/
theorem PolyZonotope.bilin_h (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.bilin f pZ₁ pZ₂ hp).h = (pZ₁.h + 1) * (pZ₂.h + 1) := rfl


-- ==================================  `PolyZonotope.bilin_q`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `q` count of `bilin`'s result. -/
theorem PolyZonotope.bilin_q (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : (PolyZonotope.bilin f pZ₁ pZ₂ hp).q = 0 := rfl

end

section

variable {α : Type} [AddCommGroup α]


-- ===============================  `PolyZonotope.compact_p_le`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)

/-- The kept factors likewise, over the columns the merge left. -/
theorem PolyZonotope.compact_p_le (pZ : PolyZonotope α) : pZ.compact.p ≤ pZ.p := by
  have h := Finset.card_le_univ (PolyZonotope.usedFactors pZ.compactGens.E)
  rw [Fintype.card_fin] at h
  exact h


-- =================================  `PolyZonotope.compact_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The independent block is untouched by either half of the compaction. -/
theorem PolyZonotope.compact_q (pZ : PolyZonotope α) : pZ.compact.q = pZ.q := rfl

end

section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `PolyZonotope.dependent_h`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `h` count of `dependent`'s result. -/
theorem PolyZonotope.dependent_h (pZ : PolyZonotope α) :
    (PolyZonotope.dependent pZ).h = pZ.h + pZ.q := rfl


-- ================================  `PolyZonotope.dependent_q`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `q` count of `dependent`'s result. -/
theorem PolyZonotope.dependent_q (pZ : PolyZonotope α) : (PolyZonotope.dependent pZ).q = 0 := rfl


-- =================================  `PolyZonotope.linComb_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `linComb`'s result. -/
theorem PolyZonotope.linComb_h (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).h = pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1) := rfl


-- =================================  `PolyZonotope.linComb_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `linComb`'s result. -/
theorem PolyZonotope.linComb_q (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).q = pZ₁.q + pZ₂.q := rfl


-- =================================  `PolyZonotope.padBack_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `h` count of `padBack`'s result. -/
theorem PolyZonotope.padBack_h (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).h = pZ.h := rfl


-- =================================  `PolyZonotope.padBack_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `q` count of `padBack`'s result. -/
theorem PolyZonotope.padBack_q (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).q = pZ.q := rfl


-- ================================  `PolyZonotope.padFront_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `h` count of `padFront`'s result. -/
theorem PolyZonotope.padFront_h (l : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padFront l pZ).h = pZ.h := rfl


-- ================================  `PolyZonotope.padFront_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [AddCommGroup α] [Module ℝ α] in
/-- The `q` count of `padFront`'s result. -/
theorem PolyZonotope.padFront_q (l : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padFront l pZ).q = pZ.q := rfl


-- ==================================  `PolyZonotope.plus_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- The `h` count of `plus`'s result. -/
theorem PolyZonotope.plus_h (pZ₁ pZ₂ : PolyZonotope α) : (pZ₁.plus pZ₂).h = pZ₁.h + pZ₂.h := rfl


-- ==================================  `PolyZonotope.plus_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

omit [Module ℝ α] in
/-- The `q` count of `plus`'s result. -/
theorem PolyZonotope.plus_q (pZ₁ pZ₂ : PolyZonotope α) : (pZ₁.plus pZ₂).q = pZ₁.q + pZ₂.q := rfl

end

section

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ===================================  `PolyZonotope.map_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `map`'s result. -/
theorem PolyZonotope.map_h (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).h = pZ.h := rfl


-- ===================================  `PolyZonotope.map_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `map`'s result. -/
theorem PolyZonotope.map_q (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).q = pZ.q := rfl

end

section

open Matrix

variable {n m : ℕ}


-- =================================  `PolyZonotope.mtimes_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `mtimes`'s result. -/
theorem PolyZonotope.mtimes_h (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).h = pZ.h := rfl


-- =================================  `PolyZonotope.mtimes_q`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `mtimes`'s result. -/
theorem PolyZonotope.mtimes_q (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).q = pZ.q := rfl

end

section

open Matrix

variable {m n : ℕ}


-- ============================  `PolyZonotope.mtimesIntervalMat_h`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `mtimesIntervalMat`'s result. -/
theorem PolyZonotope.mtimesIntervalMat_h (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : (PolyZonotope.mtimesIntervalMat IM pZ).h = pZ.h := rfl


-- ============================  `PolyZonotope.mtimesIntervalMat_q`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `mtimesIntervalMat`'s result. -/
theorem PolyZonotope.mtimesIntervalMat_q (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : (PolyZonotope.mtimesIntervalMat IM pZ).q = pZ.q + m := rfl

end

section

variable {n : ℕ}


-- ===================================  `PolyZonotope.mul_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `mul`'s result. -/
theorem PolyZonotope.mul_h (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.mul pZ₁ pZ₂ hp).h = (pZ₁.h + 1) * (pZ₂.h + 1) := rfl


-- ===================================  `PolyZonotope.mul_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `mul`'s result. -/
theorem PolyZonotope.mul_q (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.mul pZ₁ pZ₂ hp).q = 0 := rfl

end

section

variable {n m : ℕ}


-- =================================  `PolyZonotope.quadMap_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `quadMap`'s result. -/
theorem PolyZonotope.quadMap_h (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q pZ).h = (pZ.h + pZ.q + 1) * (pZ.h + pZ.q + 1) := rfl


-- =================================  `PolyZonotope.quadMap_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `quadMap`'s result. -/
theorem PolyZonotope.quadMap_q (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q pZ).q = 0 := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
