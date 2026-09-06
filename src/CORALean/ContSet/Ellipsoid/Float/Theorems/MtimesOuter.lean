import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesResidual
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

/-!
# `Ellipsoid.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box, and
the split is a zonotope's: the centre is wrong by a fixed vector, which
`residual` holds, and the generators by an entrywise amount the coefficients
scale, which `generatorError` sums.

The unit ball enters only through `‖u‖₂ ≤ 1`, and only to say `|uⱼ| ≤ 1`. The
same ball point works on both sides, so the exact layer's equality survives as
an inclusion whose entire loss is the rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image, regrouped so the centre and each generator appear once. -/
theorem Ellipsoid.aux_mulVec_nominal (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) (u : Vec ℝ E.k)
    {x : Vec ℝ n} (hx : ∀ k, x k = toReal (E.q k) + ∑ j, toReal (E.G k j) * u j) (i : Fin m) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (E.q k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (E.G k j)) * u j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (E.q k)
              + ∑ j, toReal (M i k) * toReal (E.G k j) * u j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ k, toReal (M i k) * toReal (E.q k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (E.G k j) * u j := Finset.sum_add_distrib
    _ = (∑ k, toReal (M i k) * toReal (E.q k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (E.G k j)) * u j := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm)

-- the image's nominal part, with the generator rounding charged to a box
theorem Ellipsoid.aux_mtimes_nominal (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet E ⊆
      nominalSet (Ellipsoid.mtimes M E)
        + (Ellipsoid.mtimesResidual M E).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨u, hu, hx⟩ := Ellipsoid.mem_nominalSet_iff.mp hx'
  -- the generators are wrong by this much, entrywise
  have hgen : ∀ i j, |(∑ k, toReal (M i k) * toReal (E.G k j))
      - toReal (matMulDown M E.G i j)| ≤ toReal (matMulDiff M E.G i j) := by
    intro i j
    -- ascribed, so these are about `matMul*` rather than the `dot*` they unfold to
    have hlo : toReal (matMulDown M E.G i j) ≤ ∑ k, toReal (M i k) * toReal (E.G k j) :=
      dotDown_le (M i) (fun k => E.G k j)
    have hhi : ∑ k, toReal (M i k) * toReal (E.G k j) ≤ toReal (matMulUp M E.G i j) :=
      le_dotUp (M i) (fun k => E.G k j)
    have hgap := sub_le_subUp (matMulUp M E.G i j) (matMulDown M E.G i j)
    rw [abs_le]
    exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩
  refine ⟨fun i => toReal ((Ellipsoid.mtimes M E).q i)
            + ∑ j : Fin E.k, toReal ((Ellipsoid.mtimes M E).G i j) * u j,
          Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hu, fun _ => rfl⟩,
          _, Interval.plus_outer _ _
            ⟨_, Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) E.q, le_dotUp (M i) E.q⟩),
             _, Ellipsoid.mem_generatorError hgen hu, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hsum : (∑ j, toReal (matMulDown M E.G i j) * u j)
      + (∑ j, (∑ k, toReal (M i k) * toReal (E.G k j)
          - toReal (matMulDown M E.G i j)) * u j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (E.G k j)) * u j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  show toReal ((Ellipsoid.mtimes M E).q i)
        + ∑ j : Fin E.k, toReal ((Ellipsoid.mtimes M E).G i j) * u j
      + ((∑ k, toReal (M i k) * toReal (E.q k) - toReal (mulVecDown M E.q i))
        + ∑ j, (∑ k, toReal (M i k) * toReal (E.G k j)
            - toReal (matMulDown M E.G i j)) * u j)
    = (toRealMat M *ᵥ x) i
  rw [Ellipsoid.aux_mulVec_nominal M E u hx i]
  simp only [Ellipsoid.mtimes]
  linarith [hsum]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem Ellipsoid.aux_mtimes_error (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error E).construct + (Ellipsoid.mtimesResidual M E).construct ⊆
      (error (Ellipsoid.mtimes M E)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M E.err))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mtimes_outer (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' E.construct ⊆ (Ellipsoid.mtimes M E).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (Ellipsoid.aux_mtimes_nominal M E) (Ellipsoid.aux_mtimes_error M E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
