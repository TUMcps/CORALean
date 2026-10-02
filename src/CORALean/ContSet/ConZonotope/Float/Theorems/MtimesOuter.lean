import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

/-!
# `ConZonotope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box, as for
`Zonotope.mtimes_outer`, whose regrouping lemma is stated again here for the stored centre and
generators. The constraint is on the coefficients, which the stored generators keep, so the
witness is the same coefficient family and its membership in `P` is carried over unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the centre and each generator appear once. -/
theorem ConZonotope.aux_mulVec_nominal (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) (β : Vec ℝ cZ.h)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (cZ.c k) + ∑ j, toReal (cZ.G k j) * β j) (i : Fin m) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (cZ.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (cZ.c k)
              + ∑ j, toReal (M i k) * toReal (cZ.G k j) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (cZ.c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (cZ.G k j) * β j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (cZ.c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)) * β j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

theorem ConZonotope.aux_mtimes_nominal (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet cZ ⊆
      nominalSet (ConZonotope.mtimes M cZ)
        + (Zonotope.mtimesResidual M cZ.zonotope).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  -- the point's coefficients, which the image keeps
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx'
  -- the generators are wrong by this much, entrywise
  have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (cZ.G k j))
      - toReal (matMulDown M cZ.G i j)| ≤ toReal (matMulDiff M cZ.G i j) := by
    intro i j
    -- the two directed roundings bracket the exact entry
    have hlo : toReal (matMulDown M cZ.G i j) ≤ ∑ k, toReal (M i k) * toReal (cZ.G k j) :=
      dotDown_le (M i) (fun k => cZ.G k j)
    have hhi : ∑ k, toReal (M i k) * toReal (cZ.G k j) ≤ toReal (matMulUp M cZ.G i j) :=
      le_dotUp (M i) (fun k => cZ.G k j)
    have hgap := sub_le_subUp (matMulUp M cZ.G i j) (matMulDown M cZ.G i j)
    rw [abs_le]
    exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩
  -- the stored centre and generators at the same coefficients, and the box holds the rest
  refine ⟨fun i => toReal ((ConZonotope.mtimes M cZ).c i)
            + ∑ j : Fin cZ.h, toReal ((ConZonotope.mtimes M cZ).G i j) * β j,
          ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, hP, fun _ => rfl⟩,
          _, Interval.plus_outer _ _
            ⟨_, Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) cZ.c, le_dotUp (M i) cZ.c⟩),
             _, Zonotope.mem_generatorError hgen hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hsum : (∑ j, toReal (matMulDown M cZ.G i j) * β j)
      + (∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)
          - toReal (matMulDown M cZ.G i j)) * β j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the exact image, regrouped, closes the goal
  show toReal ((ConZonotope.mtimes M cZ).c i)
        + ∑ j : Fin cZ.h, toReal ((ConZonotope.mtimes M cZ).G i j) * β j
      + ((∑ k, toReal (M i k) * toReal (cZ.c k) - toReal (mulVecDown M cZ.c i))
        + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)
            - toReal (matMulDown M cZ.G i j)) * β j)
    = (toRealMat M *ᵥ x) i
  have key : (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (cZ.c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (cZ.G k j)) * β j :=
    ConZonotope.aux_mulVec_nominal M cZ β hx i
  rw [key]
  simp only [ConZonotope.mtimes]
  linarith [hsum]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem ConZonotope.aux_mtimes_error (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error cZ).construct + (Zonotope.mtimesResidual M cZ.zonotope).construct
      ⊆ (error (ConZonotope.mtimes M cZ)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M cZ.E))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mtimes_outer (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' cZ.construct ⊆ (ConZonotope.mtimes M cZ).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (ConZonotope.aux_mtimes_nominal M cZ) (ConZonotope.aux_mtimes_error M cZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
