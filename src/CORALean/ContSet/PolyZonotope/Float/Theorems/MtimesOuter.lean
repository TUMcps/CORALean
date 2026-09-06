import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit

/-!
# `PolyZonotope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box. The
box is easy: the old one travels through the map as a box, by
`Interval.mtimes_outer`, and the spill is added on.

The nominal obligation is where the float layer pays for arithmetic rather than
bookkeeping. The centre is wrong by a fixed vector, which `residual` holds; each
generator block is wrong by an entrywise amount its coefficients then scale,
which `generatorError` sums. The dependent block's coefficients are monomials
and the independent block's are free, and the two obligations differ only in
which lemma supplies `|coefficient| ≤ 1`.

`mulVec_split` is stated at an arbitrary coefficient vector `t` for the
dependent block rather than at `monomial PZ.E a`: the regrouping is linear
algebra and knows nothing about where the coefficients came from. It carries no
`aux_` prefix and takes the three blocks loose, the constrained representation
needing the same regrouping at its own fields.
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

theorem PolyZonotope.aux_mtimes_nominal (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet PZ ⊆
      nominalSet (PolyZonotope.mtimes M PZ)
        + (PolyZonotope.mtimesResidual M PZ).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  have hres : (fun i => (∑ k, toReal (M i k) * toReal (PZ.c k))
        - toReal (mulVecDown M PZ.c i))
      ∈ (Interval.residual (mulVecDown M PZ.c) (mulVecUp M PZ.c)
          (mulVecDown M PZ.c)).construct :=
    Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) PZ.c, le_dotUp (M i) PZ.c⟩)
  -- the two generator blocks' shortfalls, each bounded by a coefficient inside `[-1,1]`
  have hdepBox : (fun i => ∑ l, ((∑ k, toReal (M i k) * toReal (PZ.G k l))
        - toReal (matMulDown M PZ.G i l)) * Real.PolyZonotope.monomial PZ.E a l)
      ∈ (PolyZonotope.generatorError (matMulDiff M PZ.G)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.matMul_close M PZ.G) ha
  have hindBox : (fun i => ∑ j, ((∑ k, toReal (M i k) * toReal (PZ.GI k j))
        - toReal (matMulDown M PZ.GI i j)) * β j)
      ∈ (PolyZonotope.generatorError (matMulDiff M PZ.GI)).construct :=
    PolyZonotope.mem_generatorError (PolyZonotope.matMul_close M PZ.GI) hβ
  refine ⟨fun i => toReal ((PolyZonotope.mtimes M PZ).c i)
            + (∑ l : Fin PZ.h, toReal ((PolyZonotope.mtimes M PZ).G i l)
                * Real.PolyZonotope.monomial PZ.E a l)
            + ∑ j : Fin PZ.q, toReal ((PolyZonotope.mtimes M PZ).GI i j) * β j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
          _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hres, _, hdepBox, rfl⟩,
            _, hindBox, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hdep : (∑ l, toReal (matMulDown M PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
      + (∑ l, ((∑ k, toReal (M i k) * toReal (PZ.G k l))
          - toReal (matMulDown M PZ.G i l)) * Real.PolyZonotope.monomial PZ.E a l)
      = ∑ l, (∑ k, toReal (M i k) * toReal (PZ.G k l))
          * Real.PolyZonotope.monomial PZ.E a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hind : (∑ j, toReal (matMulDown M PZ.GI i j) * β j)
      + (∑ j, ((∑ k, toReal (M i k) * toReal (PZ.GI k j))
          - toReal (matMulDown M PZ.GI i j)) * β j)
      = ∑ j, (∑ k, toReal (M i k) * toReal (PZ.GI k j)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so the two recombinations line up with it term by term
  show toReal ((PolyZonotope.mtimes M PZ).c i)
        + (∑ l : Fin PZ.h, toReal ((PolyZonotope.mtimes M PZ).G i l)
            * Real.PolyZonotope.monomial PZ.E a l)
        + ∑ j : Fin PZ.q, toReal ((PolyZonotope.mtimes M PZ).GI i j) * β j
      + (((∑ k, toReal (M i k) * toReal (PZ.c k)) - toReal (mulVecDown M PZ.c i)
          + ∑ l, ((∑ k, toReal (M i k) * toReal (PZ.G k l))
              - toReal (matMulDown M PZ.G i l)) * Real.PolyZonotope.monomial PZ.E a l)
        + ∑ j, ((∑ k, toReal (M i k) * toReal (PZ.GI k j))
            - toReal (matMulDown M PZ.GI i j)) * β j)
    = (toRealMat M *ᵥ x) i
  rw [PolyZonotope.mulVec_split M PZ.c PZ.G PZ.GI
    (Real.PolyZonotope.monomial PZ.E a) β hx i]
  simp only [PolyZonotope.mtimes]
  linarith [hdep, hind]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem PolyZonotope.aux_mtimes_error (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error PZ).construct + (PolyZonotope.mtimesResidual M PZ).construct ⊆
      (error (PolyZonotope.mtimes M PZ)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M PZ.err))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mtimes_outer (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) :
    (toRealMat M *ᵥ ·) '' PZ.construct ⊆ (PolyZonotope.mtimes M PZ).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (PolyZonotope.aux_mtimes_nominal M PZ) (PolyZonotope.aux_mtimes_error M PZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
