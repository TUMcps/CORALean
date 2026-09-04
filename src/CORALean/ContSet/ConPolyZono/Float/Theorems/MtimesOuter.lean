import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
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
floats. `satisfies` therefore transfers by `id`, and every lemma the polynomial
zonotope's proof used — `mulVec_split`, `matMul_close`, `mem_generatorError` —
is reused rather than restated.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem ConPolyZono.mtimes_h (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) :
    (ConPolyZono.mtimes M C).h = C.h := rfl

/-- The constraint says of the image what it said of the argument, the stored
system being the same floats over the same factors. -/
theorem ConPolyZono.satisfies_mtimes (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n)
    (a : Fin C.p → ℝ) : (ConPolyZono.mtimes M C).satisfies a ↔ C.satisfies a := Iff.rfl

theorem ConPolyZono.aux_mtimes_nominal (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet C ⊆
      nominalSet (ConPolyZono.mtimes M C) + (ConPolyZono.mtimesResidual M C).construct := by
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨a, β, ha, hβ, hsat, hx⟩ := ConPolyZono.mem_nominalSet_iff.mp hx'
  have hres : (fun i => (∑ r, toReal (M i r) * toReal (C.c r))
        - toReal (mulVecDown M C.c i))
      ∈ (Interval.residual (mulVecDown M C.c) (mulVecUp M C.c)
          (mulVecDown M C.c)).construct :=
    Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) C.c, le_dotUp (M i) C.c⟩)
  -- the two generator blocks' shortfalls, each bounded by a coefficient inside `[-1,1]`
  have hdepBox : (fun i => ∑ l, ((∑ r, toReal (M i r) * toReal (C.G r l))
        - toReal (matMulDown M C.G i l)) * Real.PolyZonotope.monomial C.E a l)
      ∈ (PolyZonotope.generatorError (matMulDiff M C.G)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.matMul_close M C.G) ha
  have hindBox : (fun i => ∑ j, ((∑ r, toReal (M i r) * toReal (C.GI r j))
        - toReal (matMulDown M C.GI i j)) * β j)
      ∈ (PolyZonotope.generatorError (matMulDiff M C.GI)).construct :=
    PolyZonotope.mem_generatorError (PolyZonotope.matMul_close M C.GI) hβ
  refine ⟨fun i => toReal ((ConPolyZono.mtimes M C).c i)
            + (∑ l : Fin C.h, toReal ((ConPolyZono.mtimes M C).G i l)
                * Real.PolyZonotope.monomial C.E a l)
            + ∑ j : Fin C.q, toReal ((ConPolyZono.mtimes M C).GI i j) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hsat, fun _ => rfl⟩,
          _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hres, _, hdepBox, rfl⟩,
            _, hindBox, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their errors recombine into the exact ones
  have hdep : (∑ l, toReal (matMulDown M C.G i l) * Real.PolyZonotope.monomial C.E a l)
      + (∑ l, ((∑ r, toReal (M i r) * toReal (C.G r l))
          - toReal (matMulDown M C.G i l)) * Real.PolyZonotope.monomial C.E a l)
      = ∑ l, (∑ r, toReal (M i r) * toReal (C.G r l))
          * Real.PolyZonotope.monomial C.E a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hind : (∑ j, toReal (matMulDown M C.GI i j) * β j)
      + (∑ j, ((∑ r, toReal (M i r) * toReal (C.GI r j))
          - toReal (matMulDown M C.GI i j)) * β j)
      = ∑ j, (∑ r, toReal (M i r) * toReal (C.GI r j)) * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so the two recombinations line up with it term by term
  show toReal ((ConPolyZono.mtimes M C).c i)
        + (∑ l : Fin C.h, toReal ((ConPolyZono.mtimes M C).G i l)
            * Real.PolyZonotope.monomial C.E a l)
        + ∑ j : Fin C.q, toReal ((ConPolyZono.mtimes M C).GI i j) * β j
      + (((∑ r, toReal (M i r) * toReal (C.c r)) - toReal (mulVecDown M C.c i)
          + ∑ l, ((∑ r, toReal (M i r) * toReal (C.G r l))
              - toReal (matMulDown M C.G i l)) * Real.PolyZonotope.monomial C.E a l)
        + ∑ j, ((∑ r, toReal (M i r) * toReal (C.GI r j))
            - toReal (matMulDown M C.GI i j)) * β j)
    = (toRealMat M *ᵥ x) i
  rw [PolyZonotope.mulVec_split M C.c C.G C.GI (Real.PolyZonotope.monomial C.E a) β hx i]
  simp only [ConPolyZono.mtimes]
  linarith [hdep, hind]

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem ConPolyZono.aux_mtimes_error (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (error C).construct + (ConPolyZono.mtimesResidual M C).construct ⊆
      (error (ConPolyZono.mtimes M C)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M C.err))
    (Interval.plus_outer _ _)

theorem ConPolyZono.mtimes_outer (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) :
    (toRealMat M *ᵥ ·) '' C.construct ⊆ (ConPolyZono.mtimes M C).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (ConPolyZono.aux_mtimes_nominal M C) (ConPolyZono.aux_mtimes_error M C)

end CORALean.Float
