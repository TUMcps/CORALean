module

public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAndAbsorb
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Float.Operations.Reindex
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCornerMem
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `ContSet/Zonotope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =======================  `Zonotope.abs_le_absBound_of_mem_nominalSet`  ======================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The corner bounds the entrywise absolute value of every point of the nominal part of `Z`. -/
theorem Zonotope.abs_le_absBound_of_mem_nominalSet (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ nominalSet Z) (j : Fin n) : |x j| ≤ (nominal Z).absBound j := by
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact CORALean.Real.Zonotope.abs_le_absBound hβ hx j

end CORALean.Float


-- =================================  `Zonotope.absorbError_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `absorbError` spends the box as `n` fresh generators -/
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope (Vec 𝕋 n)) : Z.absorbError.h = Z.h + n := rfl

end CORALean.Float


-- ===================================  `Zonotope.linComb_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- The two incoming blocks, plus one fresh generator for the segment. -/
@[simp] theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl

end CORALean.Float


-- ===================================  `Zonotope.mtimes_h`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the generator count -/
@[simp] theorem Zonotope.mtimes_h (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) :
    (Zonotope.mtimes M Z).h = Z.h := rfl

end CORALean.Float


-- ====================================  `Zonotope.plus_h`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s generator count is the sum of the two incoming ones -/
@[simp] theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl

end CORALean.Float


-- ==============================  `Zonotope.reduceAndAbsorbBy_h`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `reduceAndAbsorbBy`'s generator count is the kept block plus the box -/
@[simp] theorem Zonotope.reduceAndAbsorbBy_h (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.reduceAndAbsorbBy part).h = q + n := rfl

end CORALean.Float


-- ==================================  `Zonotope.reduceBy_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `reduceBy`'s generator count is the kept block plus the box -/
@[simp] theorem Zonotope.reduceBy_h (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : (Z.reduceBy part).h = q + n := rfl

end CORALean.Float


-- ================================  `Zonotope.reindex_nominal`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- Definitional: `nominal` reads each generator into ℝ, which commutes with
moving the coordinate axis. -/
theorem Zonotope.reindex_nominal (e : Fin m ≃ Fin n) (Z : Zonotope (Vec 𝕋 n)) :
    InflatedContSet.nominal (Z.reindex e)
      = Real.Zonotope.map (reindexLin e) (InflatedContSet.nominal Z) := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
