import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `mtimes` reaches no further than the image of its operand plus `mtimesBox`

The reverse of `mtimes_outer`. `mtimes` keeps `Z`'s own generator count, one
rounded value per generator plus one for the centre, so the same coefficients
`Z`'s point used reproduce the exact image up to exactly `mtimesBox`'s
generators — the same regrouping `mtimes_outer`'s own proof does, run in the
other direction, and the same `matMulDiff` bound `mtimes_outer` itself proves
for `mtimesResidual`, at the opposite sign. `Z`'s own error box is absorbed at
`0`, spent the same way `plus_subset_add_box` spends it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the centre and each generator appear once —
`Zonotope.aux_mulVec_nominal` in `MtimesOuter`, restated here for this file's
own use. -/
theorem Zonotope.aux_mulVec_nominal_box (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) (β : Vec ℝ Z.h)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (Z.c k) + ∑ j, toReal (Z.G k j) * β j) (i : Fin m) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (Z.c k)
              + ∑ j, toReal (M i k) * toReal (Z.G k j) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (Z.G k j) * β j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (Z.c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

/-- Each stored generator entry is wrong by at most `matMulDiff`, `mtimes_outer`'s
own bound at the opposite sign. -/
theorem Zonotope.aux_matMulDown_sub_le (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) (i : Fin m)
    (j : Fin Z.h) : |toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)|
      ≤ toReal (matMulDiff M Z.G i j) := by -- --- PROOF ---
  have hlo : toReal (matMulDown M Z.G i j) ≤ ∑ k, toReal (M i k) * toReal (Z.G k j) :=
    dotDown_le (M i) (fun k => Z.G k j)
  have hhi : ∑ k, toReal (M i k) * toReal (Z.G k j) ≤ toReal (matMulUp M Z.G i j) :=
    le_dotUp (M i) (fun k => Z.G k j)
  have hgap := sub_le_subUp (matMulUp M Z.G i j) (matMulDown M Z.G i j)
  rw [abs_le]
  exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimes` reaches no further than the image of `Z.construct`, widened by
`mtimesBox`, provided `Z` already brackets `0` in its own box. -/
theorem Zonotope.mtimes_subset_add_box (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n)
    (h : (0 : Vec ℝ n) ∈ Z.E.construct) :
    (Zonotope.mtimes M Z).construct ⊆
      (toRealMat M *ᵥ ·) '' Z.construct
        + (Zonotope.mtimesBox M Z).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  obtain ⟨β, hβ, hy₁eq⟩ := Zonotope.mem_nominalSet_iff.mp hy₁
  -- `Z`'s own point, at the coefficients `mtimes`'s stored generators used
  set x : Vec ℝ n := fun k => toReal (Z.c k) + ∑ l, toReal (Z.G k l) * β l with hxdefeq
  have hxmem : (toRealMat M *ᵥ x) ∈ (toRealMat M *ᵥ ·) '' Z.construct := by
    refine ⟨x, ?_, rfl⟩
    have hh : x + (0 : Vec ℝ n) ∈ nominalSet Z + Z.E.construct :=
      Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩) h
    rwa [add_zero] at hh
  -- the centre and each generator's rounding gap, at the same coefficients
  set g : Vec ℝ m := fun i => (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j
    with hgdefeq
  -- the centre's rounding gap, bounded in `𝕋` as `plusBox`'s is
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
  have hg2 : (fun i => ∑ j, (toReal (matMulDown M Z.G i j)
      - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j) ∈
      (Zonotope.generatorError (matMulDiff M Z.G)).construct :=
    Zonotope.mem_generatorError (fun i j => Zonotope.aux_matMulDown_sub_le M Z i j) hβ
  -- `g` and `mtimes`'s own error box, read back into `mtimesBox` by two more `⊆` steps
  have hgmem : g + y₂ ∈ (Zonotope.mtimesBox M Z).construct := by
    have hg12 : g = (fun i => toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
        + fun i => ∑ j, (toReal (matMulDown M Z.G i j)
            - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
      rw [hgdefeq]; rfl
    rw [hg12, add_assoc]
    exact Interval.plus_outer _ _
      (Set.add_mem_add hg1 (Interval.plus_outer _ _ (Set.add_mem_add hg2 hy₂)))
  refine ⟨_, hxmem, _, hgmem, ?_⟩
  funext i
  -- the exact image at `x`, regrouped so the centre and each generator appear once
  have himg : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j :=
    Zonotope.aux_mulVec_nominal_box M Z β (fun k => by rw [hxdefeq]) i
  have hy₁i : y₁ i = toReal (mulVecDown M Z.c i) + ∑ j, toReal (matMulDown M Z.G i j) * β j :=
    hy₁eq i
  show (toRealMat M *ᵥ x) i + (g i + y₂ i) = y₁ i + y₂ i
  have hgi : g i = (toReal (mulVecDown M Z.c i) - ∑ k, toReal (M i k) * toReal (Z.c k))
      + ∑ j, (toReal (matMulDown M Z.G i j) - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
    rw [hgdefeq]
  rw [himg, hgi, hy₁i]
  have hsplit : ∑ j, (toReal (matMulDown M Z.G i j)
      - ∑ k, toReal (M i k) * toReal (Z.G k j)) * β j
      = ∑ j, toReal (matMulDown M Z.G i j) * β j
        - ∑ j, (∑ k, toReal (M i k) * toReal (Z.G k j)) * β j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
