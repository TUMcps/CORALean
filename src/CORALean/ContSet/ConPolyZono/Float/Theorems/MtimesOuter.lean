import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter

/-!
# `ConPolyZono.mtimes` over-approximates the image under a linear map

`PolyZonotope.mtimes_outer`'s argument at one more field, and the extra field
costs nothing: the constraint is a statement about the factor vector, the same
factor vector witnesses the image, and the stored `A`, `b` and `EC` are the same
floats. `satisfies_mtimes` transfers by `id`, and every lemma the polynomial
zonotope's proof used — `mulVec_split`, `matMul_close`, `mem_generatorError` —
is reused rather than restated.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_mtimes_nominal (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' nominalSet cPZ ⊆
      nominalSet (ConPolyZono.mtimes M cPZ)
        + (ConPolyZono.mtimesResidual M cPZ).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨a, β, ha, hβ, hsat, hx⟩ := ConPolyZono.mem_nominalSet_iff.mp hx'
  have hres : (fun i => (∑ r, toReal (M i r) * toReal (cPZ.c r))
        - toReal (mulVecDown M cPZ.c i))
      ∈ (Interval.residual (mulVecDown M cPZ.c) (mulVecUp M cPZ.c)
          (mulVecDown M cPZ.c)).construct :=
    Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) cPZ.c, le_dotUp (M i) cPZ.c⟩)
  -- the two generator blocks' shortfalls, each bounded by a coefficient inside `[-1,1]`
  have hdepBox : (fun i => ∑ l, ((∑ r, toReal (M i r) * toReal (cPZ.G l r))
        - toReal (mulVecDown M (cPZ.G l) i)) * Real.PolyZonotope.monomial cPZ.E a l)
      ∈ (PolyZonotope.generatorError (matMulDiff M fun i l => cPZ.G l i)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.matMul_close M cPZ.G) ha
  have hindBox : (fun i => ∑ j, ((∑ r, toReal (M i r) * toReal (cPZ.GI j r))
        - toReal (mulVecDown M (cPZ.GI j) i)) * β j)
      ∈ (PolyZonotope.generatorError (matMulDiff M fun i j => cPZ.GI j i)).construct :=
    PolyZonotope.mem_generatorError (PolyZonotope.matMul_close M cPZ.GI) hβ
  refine ⟨fun i => toReal ((ConPolyZono.mtimes M cPZ).c i)
            + (∑ l : Fin cPZ.h, toReal ((ConPolyZono.mtimes M cPZ).G l i)
                * Real.PolyZonotope.monomial cPZ.E a l)
            + ∑ j : Fin cPZ.q, toReal ((ConPolyZono.mtimes M cPZ).GI j i) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hsat, fun _ => rfl⟩,
          _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hres, _, hdepBox, rfl⟩,
            _, hindBox, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hdep : (∑ l, toReal (mulVecDown M (cPZ.G l) i) * Real.PolyZonotope.monomial cPZ.E a l)
      + (∑ l, ((∑ r, toReal (M i r) * toReal (cPZ.G l r))
          - toReal (mulVecDown M (cPZ.G l) i)) * Real.PolyZonotope.monomial cPZ.E a l)
      = ∑ l, (∑ r, toReal (M i r) * toReal (cPZ.G l r))
          * Real.PolyZonotope.monomial cPZ.E a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hind : (∑ j, toReal (mulVecDown M (cPZ.GI j) i) * β j)
      + (∑ j, ((∑ r, toReal (M i r) * toReal (cPZ.GI j r))
          - toReal (mulVecDown M (cPZ.GI j) i)) * β j)
      = ∑ j, (∑ r, toReal (M i r) * toReal (cPZ.GI j r)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so the two recombinations line up with it term by term
  show toReal ((ConPolyZono.mtimes M cPZ).c i)
        + (∑ l : Fin cPZ.h, toReal ((ConPolyZono.mtimes M cPZ).G l i)
            * Real.PolyZonotope.monomial cPZ.E a l)
        + ∑ j : Fin cPZ.q, toReal ((ConPolyZono.mtimes M cPZ).GI j i) * β j
      + (((∑ r, toReal (M i r) * toReal (cPZ.c r)) - toReal (mulVecDown M cPZ.c i)
          + ∑ l, ((∑ r, toReal (M i r) * toReal (cPZ.G l r))
              - toReal (mulVecDown M (cPZ.G l) i)) * Real.PolyZonotope.monomial cPZ.E a l)
        + ∑ j, ((∑ r, toReal (M i r) * toReal (cPZ.GI j r))
            - toReal (mulVecDown M (cPZ.GI j) i)) * β j)
    = (toRealMat M *ᵥ x) i
  rw [PolyZonotope.mulVec_split M cPZ.c cPZ.G cPZ.GI (Real.PolyZonotope.monomial cPZ.E a) β hx i]
  simp only [ConPolyZono.mtimes]
  linarith [hdep, hind]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem ConPolyZono.aux_mtimes_error (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' (error cPZ).construct + (ConPolyZono.mtimesResidual M cPZ).construct ⊆
      (error (ConPolyZono.mtimes M cPZ)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M cPZ.err))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mtimes_outer (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' cPZ.construct ⊆ (ConPolyZono.mtimes M cPZ).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (ConPolyZono.aux_mtimes_nominal M cPZ) (ConPolyZono.aux_mtimes_error M cPZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
