module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAndAbsorb
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Float.Operations.Reindex
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Zonotope
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

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet Matrix Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r m : ℕ}


-- =======================  `Zonotope.abs_le_absBound_of_mem_nominalSet`  ======================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The corner bounds the entrywise absolute value of every point of the nominal part of `Z`. -/
theorem Zonotope.abs_le_absBound_of_mem_nominalSet (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ nominalSet Z) (j : Fin n) : |x j| ≤ (nominal Z).absBound j := by
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact CORALean.Real.Zonotope.abs_le_absBound hβ hx j


-- =================================  `Zonotope.absorbError_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `absorbError` spends the box as `n` fresh generators -/
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope (Vec 𝕋 n)) : Z.absorbError.h = Z.h + n := rfl


-- ===================================  `Zonotope.linComb_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- The two incoming blocks, plus one fresh generator for the segment. -/
@[simp] theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl


-- ===================================  `Zonotope.mtimes_h`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the generator count -/
@[simp] theorem Zonotope.mtimes_h (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) :
    (Zonotope.mtimes M Z).h = Z.h := rfl


-- ====================================  `Zonotope.plus_h`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s generator count is the sum of the two incoming ones -/
@[simp] theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl


-- ==============================  `Zonotope.reduceAndAbsorbBy_h`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `reduceAndAbsorbBy`'s generator count is the kept block plus the box -/
@[simp] theorem Zonotope.reduceAndAbsorbBy_h (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.reduceAndAbsorbBy part).h = q + n := rfl


-- ==================================  `Zonotope.reduceBy_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `reduceBy`'s generator count is the kept block plus the box -/
@[simp] theorem Zonotope.reduceBy_h (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : (Z.reduceBy part).h = q + n := rfl


-- ================================  `Zonotope.reindex_nominal`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---

/-- Definitional: `nominal` reads each generator into ℝ, which commutes with
moving the coordinate axis. -/
theorem Zonotope.reindex_nominal (e : Fin m ≃ Fin n) (Z : Zonotope (Vec 𝕋 n)) :
    InflatedContSet.nominal (Z.reindex e)
      = Real.Zonotope.map (reindexLin e) (InflatedContSet.nominal Z) := rfl

end CORALean.Float


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `Zonotope.materialise_eq`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem Zonotope.materialise_eq (Z : Zonotope (Vec 𝕋 n)) : Z.materialise = Z := by
  simp [Zonotope.materialise]


-- ===================================  `Zonotope.nominal_c`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal Zonotope's field `c`, so proofs can see through the instance. -/
theorem Zonotope.nominal_c [SoundFloatArithmetic 𝕋] (Z : Zonotope (Vec 𝕋 n)) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl


-- ===================================  `Zonotope.nominal_G`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal Zonotope's field `G`, so proofs can see through the instance. -/
theorem Zonotope.nominal_G [SoundFloatArithmetic 𝕋] (Z : Zonotope (Vec 𝕋 n)) :
    (InflatedContSet.nominal Z).G = fun j i => toReal (Z.G j i) := rfl


-- ===================================  `Zonotope.nominal_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal zonotope's fields, so proofs can see through the instance. -/
theorem Zonotope.nominal_h [SoundFloatArithmetic 𝕋] (Z : Zonotope (Vec 𝕋 n)) :
    (InflatedContSet.nominal Z).h = Z.h := rfl

end CORALean.Float


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}
variable {m : ℕ}


-- ===============================  `Zonotope.materialiseMat_eq`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialiseMat` is the identity: it changes only what running the definition costs. -/
@[simp] theorem Zonotope.materialiseMat_eq (Z : Zonotope (Mat 𝕋 m n)) :
    Z.materialiseMat = Z := by
  simp [Zonotope.materialiseMat]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
