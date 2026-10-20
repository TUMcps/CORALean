module

public import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `ConZonotope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box, as for
`Zonotope.mtimes_outer`, whose regrouping lemma is stated again here for the stored center and
generators. The constraint is on the coefficients, which the stored generators keep, so the
witness is the same coefficient family and its membership in `P` is carried over unchanged.

## Inputs
* `M` – matrix
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* the image under the matrix is contained in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the center and each generator appear once. -/
theorem ConZonotope.aux_mulVec_nominal (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (β : Vec ℝ cZ.h)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (cZ.c k) + ∑ j, toReal (cZ.G j k) * β j)
    (i : Fin m) : -- --- CONCL ---
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (cZ.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (cZ.c k)
              + ∑ j, toReal (M i k) * toReal (cZ.G j k) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (cZ.c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (cZ.G j k) * β j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (cZ.c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)) * β j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

theorem ConZonotope.aux_mtimes_nominal (M : Mat 𝕋 m n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    (toRealMat M *ᵥ ·) '' nominalSet cZ ⊆
      nominalSet (ConZonotope.mtimes M cZ)
        + (Zonotope.mtimesResidual M cZ.zonotope).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  -- the point's coefficients, which the image keeps
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx'
  -- the generators are wrong by this much, entrywise
  have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (cZ.G j k))
      - toReal (mulVecDown M (cZ.G j) i)| ≤ toReal (matMulDiff M (fun i j => cZ.G j i) i j) := by
    intro i j
    -- the two directed roundings bracket the exact entry
    have hlo : toReal (mulVecDown M (cZ.G j) i) ≤ ∑ k, toReal (M i k) * toReal (cZ.G j k) :=
      dotDown_le (M i) (fun k => cZ.G j k)
    have hhi : ∑ k, toReal (M i k) * toReal (cZ.G j k) ≤ toReal (mulVecUp M (cZ.G j) i) :=
      le_dotUp (M i) (fun k => cZ.G j k)
    have hgap := sub_le_subUp (mulVecUp M (cZ.G j) i) (mulVecDown M (cZ.G j) i)
    change _ ≤ toReal (subUp (mulVecUp M (cZ.G j) i) (mulVecDown M (cZ.G j) i))
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- the stored center and generators at the same coefficients, and the box holds the rest
  refine ⟨fun i => toReal ((ConZonotope.mtimes M cZ).c i)
            + ∑ j : Fin cZ.h, toReal ((ConZonotope.mtimes M cZ).G j i) * β j,
          ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, hP, fun _ => rfl⟩,
          _, Interval.plus_outer _ _
            ⟨_, Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) cZ.c, le_dotUp (M i) cZ.c⟩),
             _, Zonotope.mem_generatorError hgen hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hsum : (∑ j, toReal (mulVecDown M (cZ.G j) i) * β j)
      + (∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)
          - toReal (mulVecDown M (cZ.G j) i)) * β j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the exact image, regrouped, closes the goal
  show toReal ((ConZonotope.mtimes M cZ).c i)
        + ∑ j : Fin cZ.h, toReal ((ConZonotope.mtimes M cZ).G j i) * β j
      + ((∑ k, toReal (M i k) * toReal (cZ.c k) - toReal (mulVecDown M cZ.c i))
        + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)
            - toReal (mulVecDown M (cZ.G j) i)) * β j)
    = (toRealMat M *ᵥ x) i
  have key : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (cZ.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G j k)) * β j :=
    ConZonotope.aux_mulVec_nominal M cZ β hx i
  rw [key]
  simp only [ConZonotope.mtimes]
  linarith [hsum]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem ConZonotope.aux_mtimes_error (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' (I_error cZ).construct + (Zonotope.mtimesResidual M cZ.zonotope).construct
      ⊆ (I_error (ConZonotope.mtimes M cZ)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M cZ.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mtimes_outer (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' cZ.construct ⊆ (ConZonotope.mtimes M cZ).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (ConZonotope.aux_mtimes_nominal M cZ) (ConZonotope.aux_mtimes_error M cZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
