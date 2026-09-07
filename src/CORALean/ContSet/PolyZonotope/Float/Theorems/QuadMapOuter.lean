import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact

/-!
# `PolyZonotope.quadMap` over-approximates the image under a quadratic map

The exact layer proves the hard half — that the image of a polynomial zonotope
under a quadratic map *is* a polynomial zonotope — and this file adds only what
rounding costs. `dependent` runs first and leaves a set with no independent
block and no error box, so `quadMapDep_exact` applies to the nominal part as it
stands; from there the two representations differ in their generator entries
alone, and `generatorError` prices that difference exactly as it does for
`mtimes`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-! ## What a rounded bilinear form costs -/


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_quadMapG_close (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope 𝕋 n)
    (i : Fin m) (l : Fin ((pZ.h + 1) * (pZ.h + 1))) :
    |Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
        - toReal (PolyZonotope.quadMapGDown Q pZ i l)|
      ≤ toReal (PolyZonotope.quadMapGDiff Q pZ i l) := by -- --- PROOF ---
  set l₁ := (finProdFinEquiv.symm l).1 with hl₁
  set l₂ := (finProdFinEquiv.symm l).2 with hl₂
  -- the exact bilinear form, with both vectors read back through `toReal`
  have hexact : Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
      = ∑ r, toReal (PolyZonotope.extG pZ r l₁)
          * ∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ r' l₂) := by
    show (∑ r, Real.PolyZonotope.extG (nominal pZ) l₁ r
        * ∑ r', toRealMat (Q i) r r' * Real.PolyZonotope.extG (nominal pZ) l₂ r') = _
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [PolyZonotope.toReal_extG pZ r l₁]
    exact congrArg _ (Finset.sum_congr rfl fun r' _ => by
      rw [PolyZonotope.toReal_extG pZ r' l₂]; rfl)
  have hw : ∀ r, toReal (mulVecDown (Q i) (fun r' => PolyZonotope.extG pZ r' l₂) r)
        ≤ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ r' l₂))
      ∧ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ r' l₂))
        ≤ toReal (mulVecUp (Q i) (fun r' => PolyZonotope.extG pZ r' l₂) r) :=
    fun r => ⟨dotDown_le (Q i r) _, le_dotUp (Q i r) _⟩
  -- the middle vector enters as a pair of bounds, picked per term, bracketing the bilinear form
  have hlo := PolyZonotope.quadDown_le
    (g := fun r => PolyZonotope.extG pZ r l₁) hw
  have hhi := PolyZonotope.le_quadUp
    (g := fun r => PolyZonotope.extG pZ r l₁) hw
  have hgap := sub_le_subUp (PolyZonotope.quadMapGUp Q pZ i l)
    (PolyZonotope.quadMapGDown Q pZ i l)
  rw [hexact, abs_le]
  constructor
  · simp only [PolyZonotope.quadMapGDiff]
    simp only [PolyZonotope.quadMapGDown, PolyZonotope.quadMapGUp] at hlo hhi hgap ⊢
    linarith
  · simp only [PolyZonotope.quadMapGDiff]
    simp only [PolyZonotope.quadMapGDown, PolyZonotope.quadMapGUp] at hlo hhi hgap ⊢
    linarith

/-! ## The refinement -/

theorem PolyZonotope.aux_quadMapDep_refines (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope 𝕋 n) :
    (Real.PolyZonotope.quadMapDep (fun k => toRealMat (Q k)) (nominal pZ)).construct
      ⊆ (PolyZonotope.quadMapDep Q pZ).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, b, ha, hb, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  have hbox : (fun i => ∑ l,
        (Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
          - toReal (PolyZonotope.quadMapGDown Q pZ i l))
            * Real.PolyZonotope.monomial (PolyZonotope.quadMapE pZ) a l)
      ∈ (PolyZonotope.generatorError (PolyZonotope.quadMapGDiff Q pZ)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.aux_quadMapG_close Q pZ) ha
  -- counts ascribed: through the projection they agree only after unfolding `quadMapDep`
  refine ⟨fun i => toReal ((PolyZonotope.quadMapDep Q pZ).c i)
            + (∑ l : Fin ((pZ.h + 1) * (pZ.h + 1)), toReal (PolyZonotope.quadMapGDown Q pZ i l)
                * Real.PolyZonotope.monomial (PolyZonotope.quadMapE pZ) a l)
            + ∑ j : Fin 0, toReal ((PolyZonotope.quadMapDep Q pZ).GI i j) * b j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, b, ha, hb, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- binders ascribed: the two layers' counts are one number but not the term `rw` matches
  have hsum : (∑ l : Fin ((pZ.h + 1) * (pZ.h + 1)), toReal (PolyZonotope.quadMapGDown Q pZ i l)
        * Real.PolyZonotope.monomial (PolyZonotope.quadMapE pZ) a l)
      + (∑ l : Fin ((pZ.h + 1) * (pZ.h + 1)),
          (Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
            - toReal (PolyZonotope.quadMapGDown Q pZ i l))
              * Real.PolyZonotope.monomial (PolyZonotope.quadMapE pZ) a l)
      = ∑ l : Fin ((pZ.h + 1) * (pZ.h + 1)),
          Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
            * Real.PolyZonotope.monomial (PolyZonotope.quadMapE pZ) a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Pi.add_apply, PolyZonotope.quadMapDep, toReal_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  rw [hx i]
  simp only [Real.PolyZonotope.quadMapDep, Real.PolyZonotope.bilin, Pi.zero_apply,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  exact hsum


-- =======================================  MAIN THEOREM  ======================================= --

-- the whole operation: `dependent` first, then the exact map, then this refinement
theorem PolyZonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope 𝕋 n) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' pZ.construct
      ⊆ (PolyZonotope.quadMap Q pZ).construct := by
  refine subset_trans (Set.image_mono (PolyZonotope.dependent_nominal pZ)) ?_
  refine subset_trans ?_ (PolyZonotope.aux_quadMapDep_refines Q pZ.dependent)
  exact (Real.PolyZonotope.quadMapDep_exact (fun k => toRealMat (Q k))
    (nominal pZ.dependent) rfl).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
