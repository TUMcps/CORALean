module

public import CORALean.ContSet.ConZonotope.Float.Theorems.FourierMotzkinIterOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalTight
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter

@[expose] public section

/-!
# The box that keeps the constraints holds the constrained zonotope

A point is `c + G β + e` with `β` meeting the nominal constraint and `e` in the error box. The
coefficients meet the folded rows (`absorbRounding_outer`, the slacks only), so
`ConZonotope.fourierMotzkinIter_outer` keeps them in the box `J`; the float image of `J` holds
`G β` (`Zonotope.mtimes_outer`), and `c + e` lies in the box the center and the error box span.
Outer for every `k`.

## Inputs
* `k` – number of contraction passes
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* the set lies in `ConZonotope.intervalTight k cZ`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intervalTight_contains (k : ℕ) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    cZ.toSet ⊆ (cZ.intervalTight k).toSet := by -- --- PROOF ---
  -- the folded rows of the constraint, as the box reads them
  let Q : HPolytope 𝕋 (Vec 𝕋 cZ.h) := ({ cZ.P with I_error := Interval.origin cZ.h } :
    HPolytope 𝕋 (Vec 𝕋 cZ.h)).absorbRounding
  -- a point is `y + e`, `y = c + G β` with `β` meeting the nominal constraint
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨β, hβ, hβP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hy
  -- the coefficients meet the folded rows
  have h0 : (0 : Vec ℝ cZ.h) ∈ (Interval.origin cZ.h : Interval (Vec 𝕋 cZ.h)).toSet := fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ cZ.h) i ∧ (0 : Vec ℝ cZ.h) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  have hβQ : β ∈ Q.toSet :=
    HPolytope.absorbRounding_outer _ ⟨β, hβP, 0, h0, add_zero β⟩
  have hrows := ((HPolytope.mem_toSet_iff (HPolytope.isErrFree_of_origin rfl rfl rfl)).mp hβQ).1
  -- the box of the coefficients, the float image of it, and the center with the error
  have hJ := ConZonotope.fourierMotzkinIter_outer Q.A Q.b k hβ
    hrows
  have hG := Zonotope.mtimes_outer (fun i j => cZ.G j i) (ConZonotope.fourierMotzkinIter
    Q.A Q.b k).zonotope
    (Set.mem_image_of_mem _ (Interval.zonotope_contains _ hJ))
  have hGJ := Zonotope.interval_contains _ hG
  have hce : (fun i => toReal (cZ.c i) + e i) ∈ (⟨fun i => addDown (cZ.c i) (cZ.I_error.inf i),
      fun i => addUp (cZ.c i) (cZ.I_error.sup i)⟩ : Interval (Vec 𝕋 n)).toSet :=
    Interval.mem_vec_iff.mpr fun i => by
      obtain ⟨h1, h2⟩ := Interval.mem_vec_iff.mp he i
      replace h1 : toReal (cZ.I_error.inf i) ≤ e i := h1
      replace h2 : e i ≤ toReal (cZ.I_error.sup i) := h2
      exact ⟨le_trans (addDown_le_add _ _) (by linarith),
        le_trans (by linarith) (add_le_addUp _ _)⟩
  -- the point splits as the image of the box plus the center with the error
  have hsum : y + e =
      (toRealMat (fun i j => cZ.G j i) *ᵥ β) + (fun i => toReal (cZ.c i) + e i) := by
    funext i
    simp only [Pi.add_apply, hval i]
    simp [Matrix.mulVec, dotProduct]
    change toReal (cZ.c i) + ∑ x, toReal (cZ.G x i) * β x + e i =
      ∑ x, toReal (cZ.G x i) * β x + (toReal (cZ.c i) + e i)
    ring
  show y + e ∈ _
  rw [hsum]
  exact Interval.plus_outer _ _ (Set.add_mem_add hGJ hce)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
