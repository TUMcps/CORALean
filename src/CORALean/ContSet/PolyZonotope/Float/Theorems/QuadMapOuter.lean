import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
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

The exponent matrices need no comparison at all: `quadMapE` is `rfl`-equal
across the layers, being a sum of naturals either way. That is the whole reason
this file is about arithmetic and not about monomials.

`aux_min_mul_le` and `aux_le_max_mul` are the one place a sign is examined:
`Q *ᵥ Gⱼ` is known to an interval, and which endpoint of `Gᵢ(r) · [lo, hi]` is
the larger depends on the sign of `Gᵢ(r)`. Taking both and picking with
`min`/`max` is how the layer avoids ever asking.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-! ## A product against an interval -/

theorem PolyZonotope.aux_min_mul_le {a lo hi w : ℝ} (h1 : lo ≤ w) (h2 : w ≤ hi) :
    min (a * lo) (a * hi) ≤ a * w := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 ha)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 ha)

theorem PolyZonotope.aux_le_max_mul {a lo hi w : ℝ} (h1 : lo ≤ w) (h2 : w ≤ hi) :
    a * w ≤ max (a * lo) (a * hi) := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_max_left _ _)

-- so a directed sum of per-term extremes brackets the exact bilinear value
theorem PolyZonotope.quadDown_le {g wlo whi : Vec 𝕋 n} {w : Vec ℝ n}
    (hw : ∀ r, toReal (wlo r) ≤ w r ∧ w r ≤ toReal (whi r)) :
    toReal (PolyZonotope.quadDown g wlo whi) ≤ ∑ r, toReal (g r) * w r := by
  refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun r _ => ?_)
  rw [toReal_minimum]
  exact le_trans (min_le_min (mulDown_le_mul _ _) (mulDown_le_mul _ _))
    (PolyZonotope.aux_min_mul_le (hw r).1 (hw r).2)

theorem PolyZonotope.le_quadUp {g wlo whi : Vec 𝕋 n} {w : Vec ℝ n}
    (hw : ∀ r, toReal (wlo r) ≤ w r ∧ w r ≤ toReal (whi r)) :
    (∑ r, toReal (g r) * w r) ≤ toReal (PolyZonotope.quadUp g wlo whi) := by
  refine le_trans (Finset.sum_le_sum fun r _ => ?_) (sum_le_sumUp _)
  rw [toReal_maximum]
  exact le_trans (PolyZonotope.aux_le_max_mul (hw r).1 (hw r).2)
    (max_le_max (mul_le_mulUp _ _) (mul_le_mulUp _ _))

/-! ## Reading the widened data as the exact layer's -/

theorem PolyZonotope.toReal_extG (S : PolyZonotope 𝕋 n) (i : Fin n) (l : Fin (S.h + 1)) :
    toReal (PolyZonotope.extG S i l) = Real.PolyZonotope.extG (nominal S) l i := by
  refine Fin.cases ?_ (fun l' => ?_) l
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_zero]
    rfl
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_succ]
    rfl

/-- The exponent bookkeeping is the same term in both layers. -/
theorem PolyZonotope.quadMapE_nominal (S : PolyZonotope 𝕋 n) :
    PolyZonotope.quadMapE S = Real.PolyZonotope.quadMapE (nominal S) := rfl

/-! ## What a rounded bilinear form costs -/

theorem PolyZonotope.aux_quadMapG_close (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n)
    (i : Fin m) (l : Fin ((S.h + 1) * (S.h + 1))) :
    |Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal S) l i
        - toReal (PolyZonotope.quadMapGDown Q S i l)|
      ≤ toReal (PolyZonotope.quadMapGDiff Q S i l) := by
  set l₁ := (finProdFinEquiv.symm l).1 with hl₁
  set l₂ := (finProdFinEquiv.symm l).2 with hl₂
  -- the exact bilinear form, with both vectors read back through `toReal`
  have hexact : Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal S) l i
      = ∑ r, toReal (PolyZonotope.extG S r l₁)
          * ∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG S r' l₂) := by
    show (∑ r, Real.PolyZonotope.extG (nominal S) l₁ r
        * ∑ r', toRealMat (Q i) r r' * Real.PolyZonotope.extG (nominal S) l₂ r') = _
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [PolyZonotope.toReal_extG S r l₁]
    exact congrArg _ (Finset.sum_congr rfl fun r' _ => by
      rw [PolyZonotope.toReal_extG S r' l₂]; rfl)
  have hw : ∀ r, toReal (mulVecDown (Q i) (fun r' => PolyZonotope.extG S r' l₂) r)
        ≤ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG S r' l₂))
      ∧ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG S r' l₂))
        ≤ toReal (mulVecUp (Q i) (fun r' => PolyZonotope.extG S r' l₂) r) :=
    fun r => ⟨dotDown_le (Q i r) _, le_dotUp (Q i r) _⟩
  -- the middle vector enters as a pair of bounds, picked per term
  have hlo := PolyZonotope.quadDown_le
    (g := fun r => PolyZonotope.extG S r l₁) hw
  have hhi := PolyZonotope.le_quadUp
    (g := fun r => PolyZonotope.extG S r l₁) hw
  have hgap := sub_le_subUp (PolyZonotope.quadMapGUp Q S i l)
    (PolyZonotope.quadMapGDown Q S i l)
  rw [hexact, abs_le]
  constructor
  · simp only [PolyZonotope.quadMapGDiff]
    simp only [PolyZonotope.quadMapGDown, PolyZonotope.quadMapGUp] at hlo hhi hgap ⊢
    linarith
  · simp only [PolyZonotope.quadMapGDiff]
    simp only [PolyZonotope.quadMapGDown, PolyZonotope.quadMapGUp] at hlo hhi hgap ⊢
    linarith

/-! ## The refinement -/

theorem PolyZonotope.aux_quadMapDep_refines (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    (Real.PolyZonotope.quadMapDep (fun k => toRealMat (Q k)) (nominal S)).construct
      ⊆ (PolyZonotope.quadMapDep Q S).construct := by
  intro x hx
  obtain ⟨a, b, ha, hb, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  have hbox : (fun i => ∑ l,
        (Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal S) l i
          - toReal (PolyZonotope.quadMapGDown Q S i l))
            * Real.PolyZonotope.monomial (PolyZonotope.quadMapE S) a l)
      ∈ (PolyZonotope.generatorError (PolyZonotope.quadMapGDiff Q S)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.aux_quadMapG_close Q S) ha
  -- counts ascribed: through the projection they agree only after unfolding `quadMapDep`
  refine ⟨fun i => toReal ((PolyZonotope.quadMapDep Q S).c i)
            + (∑ l : Fin ((S.h + 1) * (S.h + 1)), toReal (PolyZonotope.quadMapGDown Q S i l)
                * Real.PolyZonotope.monomial (PolyZonotope.quadMapE S) a l)
            + ∑ j : Fin 0, toReal ((PolyZonotope.quadMapDep Q S).GI i j) * b j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, b, ha, hb, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- binders ascribed: the two layers' counts are one number but not the term `rw` matches
  have hsum : (∑ l : Fin ((S.h + 1) * (S.h + 1)), toReal (PolyZonotope.quadMapGDown Q S i l)
        * Real.PolyZonotope.monomial (PolyZonotope.quadMapE S) a l)
      + (∑ l : Fin ((S.h + 1) * (S.h + 1)),
          (Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal S) l i
            - toReal (PolyZonotope.quadMapGDown Q S i l))
              * Real.PolyZonotope.monomial (PolyZonotope.quadMapE S) a l)
      = ∑ l : Fin ((S.h + 1) * (S.h + 1)),
          Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal S) l i
            * Real.PolyZonotope.monomial (PolyZonotope.quadMapE S) a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Pi.add_apply, PolyZonotope.quadMapDep, toReal_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  rw [hx i]
  simp only [Real.PolyZonotope.quadMapDep, Pi.zero_apply, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  exact hsum

-- the whole operation: `dependent` first, then the exact map, then this refinement
theorem PolyZonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (PZ : PolyZonotope 𝕋 n) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' PZ.construct
      ⊆ (PolyZonotope.quadMap Q PZ).construct := by
  refine subset_trans (Set.image_mono (PolyZonotope.dependent_nominal PZ)) ?_
  refine subset_trans ?_ (PolyZonotope.aux_quadMapDep_refines Q PZ.dependent)
  exact (Real.PolyZonotope.quadMapDep_exact (fun k => toRealMat (Q k))
    (nominal PZ.dependent) rfl).subset

end CORALean.Float
