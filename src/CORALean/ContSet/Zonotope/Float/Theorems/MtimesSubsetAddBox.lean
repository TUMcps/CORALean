module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `mtimes` reaches no further than the image of its operand plus `mtimesBox`

The reverse of `mtimes_outer`. Every point of `mtimes M Z` is a point of `M Z` plus a point of
`mtimesBox M Z`.

The proof takes a point of `mtimes M Z` with its coefficients. The same coefficients give a
point of `Z`, and `M` maps it to a point of `M Z`. What is left over is the rounding error of the
center and of each generator, and `mtimesBox` contains it. This is the argument of
`mtimes_outer` read backwards, with the same `matMulDiff` bound at the opposite sign. The error
box of `Z` is not needed here: its zero point is used, as in `plus_subset_add_box`.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the center and each generator appear once —
`Zonotope.aux_mulVec_nominal` in `MtimesOuter`, restated here for this file's
own use. -/
theorem Zonotope.aux_mulVec_nominal_box (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) (β : Vec ℝ Z.h)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (Z.c k) + ∑ j, toReal (Z.G j k) * β j) (i : Fin m) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (Z.c k)
              + ∑ j, toReal (M i k) * toReal (Z.G j k) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (Z.G j k) * β j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

/-- Each stored generator entry is wrong by at most `matMulDiff`, `mtimes_outer`'s
own bound at the opposite sign. -/
theorem Zonotope.aux_matMulDown_sub_le (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) (i : Fin m)
    (j : Fin Z.h) :
    |toReal (matMulDown M (fun i j => Z.G j i) i j) - ∑ k, toReal (M i k) * toReal (Z.G j k)|
      ≤ toReal (matMulDiff M (fun i j => Z.G j i) i j) := by -- --- PROOF ---
  have hlo : toReal (matMulDown M (fun i j => Z.G j i) i j)
      ≤ ∑ k, toReal (M i k) * toReal (Z.G j k) :=
    dotDown_le (M i) (fun k => Z.G j k)
  have hhi : ∑ k, toReal (M i k) * toReal (Z.G j k)
      ≤ toReal (matMulUp M (fun i j => Z.G j i) i j) :=
    le_dotUp (M i) (fun k => Z.G j k)
  have hgap := sub_le_subUp (matMulUp M (fun i j => Z.G j i) i j)
    (matMulDown M (fun i j => Z.G j i) i j)
  rw [abs_le]
  exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `mtimes M Z` is a point of `M Z` plus a point of `mtimesBox M Z`.

This needs `0` to lie in the error box of `Z`. -/
theorem Zonotope.mtimes_subset_add_box (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n))
    (h : (0 : Vec ℝ n) ∈ Z.I_error.construct) :
    (Zonotope.mtimes M Z).construct ⊆
      (toRealMat M *ᵥ ·) '' Z.construct
        + (Zonotope.mtimesBox M Z).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  obtain ⟨β, hβ, hy₁eq⟩ := Zonotope.mem_nominalSet_iff.mp hy₁
  -- `Z`'s own point, at the coefficients `mtimes`'s stored generators used
  set x : Vec ℝ n := fun k => toReal (Z.c k) + ∑ l, toReal (Z.G l k) * β l with hxdefeq
  have hxmem : (toRealMat M *ᵥ x) ∈ (toRealMat M *ᵥ ·) '' Z.construct := by
    refine ⟨x, ?_, rfl⟩
    have hh : x + (0 : Vec ℝ n) ∈ nominalSet Z + Z.I_error.construct :=
      Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩) h
    rwa [add_zero] at hh
  -- the center and each generator's rounding gap, at the same coefficients
  set g : Vec ℝ m := fun i => (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M (fun i j => Z.G j i) i j)
        - ∑ k, toReal (M i k) * toReal (Z.G j k)) * β j
    with hgdefeq
  -- the center's rounding gap, bounded in `𝕋` as `plusBox`'s is
  have hg1 : (fun i => toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k)) ∈
      (⟨fun i => subDown (mulVecDown M Z.c i) (mulVecUp M Z.c i), fun _ => (zero : 𝕋)⟩ :
        Interval (Vec 𝕋 m)).construct := fun i =>
    ⟨by show toReal (subDown (mulVecDown M Z.c i) (mulVecUp M Z.c i)) ≤
          toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k)
        have h1 := subDown_le_sub (mulVecDown M Z.c i) (mulVecUp M Z.c i)
        have h2 : (∑ k, toReal (M i k) * toReal (Z.c k)) ≤ toReal (mulVecUp M Z.c i) :=
          le_dotUp (M i) Z.c
        linarith,
     by show toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k)
          ≤ toReal (zero : 𝕋)
        have h3 : toReal (mulVecDown M Z.c i) ≤ ∑ k, toReal (M i k) * toReal (Z.c k) :=
          dotDown_le (M i) Z.c
        rw [toReal_zero]; linarith⟩
  -- each generator's rounding gap, scaled by the same coefficients `β`
  have hg2 : (fun i => ∑ j, (toReal (matMulDown M (fun i j => Z.G j i) i j)
      - ∑ k, toReal (M i k) * toReal (Z.G j k)) * β j) ∈
      (Zonotope.generatorError (matMulDiff M (fun i j => Z.G j i))).construct :=
    Zonotope.mem_generatorError (fun i j => Zonotope.aux_matMulDown_sub_le M Z i j) hβ
  -- `g` and `mtimes`'s own error box, read back into `mtimesBox` by two more `⊆` steps
  have hgmem : g + y₂ ∈ (Zonotope.mtimesBox M Z).construct := by
    have hg12 : g = (fun i => toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
        + fun i => ∑ j, (toReal (matMulDown M (fun i j => Z.G j i) i j)
            - ∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by
      rw [hgdefeq]; rfl
    rw [hg12, add_assoc]
    exact Interval.plus_outer _ _
      (Set.add_mem_add hg1 (Interval.plus_outer _ _ (Set.add_mem_add hg2 hy₂)))
  refine ⟨_, hxmem, _, hgmem, ?_⟩
  funext i
  -- the exact image at `x`, regrouped so the center and each generator appear once
  have himg : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j :=
    Zonotope.aux_mulVec_nominal_box M Z β (fun k => by rw [hxdefeq]) i
  have hy₁i : y₁ i = toReal (mulVecDown M Z.c i)
      + ∑ j, toReal (matMulDown M (fun i j => Z.G j i) i j) * β j :=
    hy₁eq i
  show (toRealMat M *ᵥ x) i + (g i + y₂ i) = y₁ i + y₂ i
  have hgi : g i = (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M (fun i j => Z.G j i) i j)
        - ∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by
    rw [hgdefeq]
  rw [himg, hgi, hy₁i]
  -- the stored generators' sum, less their gaps, is the exact one
  have hsplit : ∑ j, (toReal (matMulDown M (fun i j => Z.G j i) i j)
      - ∑ k, toReal (M i k) * toReal (Z.G j k)) * β j
      = ∑ j, toReal (matMulDown M (fun i j => Z.G j i) i j) * β j
        - ∑ j, (∑ k, toReal (M i k) * toReal (Z.G j k)) * β j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
