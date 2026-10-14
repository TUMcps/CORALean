module

public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit

@[expose] public section

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
dependent block rather than at `monomial pZ.E a`: the regrouping is linear
algebra and knows nothing about where the coefficients came from. It carries no
`aux_` prefix and takes the three blocks loose, the constrained representation
needing the same regrouping at its own fields.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_mtimes_nominal (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' nominalSet pZ ⊆
      nominalSet (PolyZonotope.mtimes M pZ)
        + (PolyZonotope.mtimesResidual M pZ).construct := by -- --- PROOF ---
  -- the exact product of a column with row `i` of `M`, and what its stored rounding is short
  set ex : Vec 𝕋 n → Fin m → ℝ := fun g i => ∑ k, toReal (M i k) * toReal (g k)
  set gap : Vec 𝕋 n → Fin m → ℝ := fun g i => ex g i - toReal (mulVecDown M g i)
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  have hres : (fun i => gap pZ.c i)
      ∈ (Interval.residual (mulVecDown M pZ.c) (mulVecUp M pZ.c)
          (mulVecDown M pZ.c)).construct :=
    Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) pZ.c, le_dotUp (M i) pZ.c⟩)
  -- the two generator blocks' shortfalls, each bounded by a coefficient inside `[-1,1]`
  have hdepBox : (fun i => ∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
      ∈ (PolyZonotope.generatorError (matMulDiff M (fun i l => pZ.G l i))).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.matMul_close M pZ.G) ha
  have hindBox : (fun i => ∑ j, gap (pZ.GI j) i * β j)
      ∈ (PolyZonotope.generatorError (matMulDiff M (fun i j => pZ.GI j i))).construct :=
    PolyZonotope.mem_generatorError (PolyZonotope.matMul_close M pZ.GI) hβ
  refine ⟨fun i => toReal ((PolyZonotope.mtimes M pZ).c i)
            + (∑ l : Fin pZ.h, toReal ((PolyZonotope.mtimes M pZ).G l i)
                * Real.PolyZonotope.monomial pZ.E a l)
            + ∑ j : Fin pZ.q, toReal ((PolyZonotope.mtimes M pZ).GI j i) * β j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
          _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hres, _, hdepBox, rfl⟩,
            _, hindBox, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hdep : (∑ l, toReal (mulVecDown M (pZ.G l) i) * Real.PolyZonotope.monomial pZ.E a l)
      + (∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
      = ∑ l, ex (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hind : (∑ j, toReal (mulVecDown M (pZ.GI j) i) * β j) + (∑ j, gap (pZ.GI j) i * β j)
      = ∑ j, ex (pZ.GI j) i * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so the two recombinations line up with it term by term
  show toReal ((PolyZonotope.mtimes M pZ).c i)
        + (∑ l : Fin pZ.h, toReal ((PolyZonotope.mtimes M pZ).G l i)
            * Real.PolyZonotope.monomial pZ.E a l)
        + ∑ j : Fin pZ.q, toReal ((PolyZonotope.mtimes M pZ).GI j i) * β j
      + ((gap pZ.c i + ∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
        + ∑ j, gap (pZ.GI j) i * β j)
    = (toRealMat M *ᵥ x) i
  rw [PolyZonotope.mulVec_split M pZ.c pZ.G pZ.GI (Real.PolyZonotope.monomial pZ.E a) β hx i]
  simp only [PolyZonotope.mtimes]
  linarith [hdep, hind]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem PolyZonotope.aux_mtimes_error (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' (I_error pZ).construct + (PolyZonotope.mtimesResidual M pZ).construct ⊆
      (I_error (PolyZonotope.mtimes M pZ)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M pZ.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mtimes_outer (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' pZ.construct ⊆ (PolyZonotope.mtimes M pZ).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (PolyZonotope.aux_mtimes_nominal M pZ) (PolyZonotope.aux_mtimes_error M pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
