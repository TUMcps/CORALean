import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact

/-!
# `PolyZonotope.mul` encloses the exact product over shared factors

The exact layer proves what the operation is — the image of the shared factors
under `a ↦ point S₁ a ⊙ point S₂ a` — and this file adds only what rounding
costs. The input is the two nominal sets: `mul` is an operation on sets whose
independent block and error box `dependent` has already emptied, and from there
the two layers differ in their generator entries alone, which `generatorError`
prices exactly as it does for `mtimes` and `quadMap`.

One rounded product per entry, so `mulDown` and `mulUp` bracket the exact one
with nothing in between — the whole difference from `quadMap`, whose bilinear
form has to carry its middle vector as an interval.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## What a rounded product costs -/

theorem PolyZonotope.aux_mulG_close (S₁ S₂ : PolyZonotope 𝕋 n) (i : Fin n)
    (l : Fin ((S₁.h + 1) * (S₂.h + 1))) :
    |Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
        - toReal (PolyZonotope.mulGDown S₁ S₂ i l)|
      ≤ toReal (PolyZonotope.mulGDiff S₁ S₂ i l) := by
  have hexact : Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
      = toReal (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
        * toReal (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2) := by
    simp only [Real.PolyZonotope.mulG, PolyZonotope.toReal_extG]
  -- the two directed products bracket the exact one, and `subUp` covers the gap
  have hlo := mulDown_le_mul (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)
  have hhi := mul_le_mulUp (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)
  have hgap := sub_le_subUp (PolyZonotope.mulGUp S₁ S₂ i l) (PolyZonotope.mulGDown S₁ S₂ i l)
  rw [hexact, abs_le]
  simp only [PolyZonotope.mulGDiff, PolyZonotope.mulGDown, PolyZonotope.mulGUp] at hlo hhi hgap ⊢
  constructor <;> linarith

/-! ## The refinement -/

theorem PolyZonotope.aux_mul_refines (S₁ S₂ : PolyZonotope 𝕋 n) (hp : S₁.p = S₂.p) :
    (Real.PolyZonotope.mul (nominal S₁) (nominal S₂) hp).construct
      ⊆ (PolyZonotope.mul S₁ S₂ hp).construct := by
  intro x hx
  obtain ⟨a, b, ha, hb, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  have hbox : (fun i => ∑ l,
        (Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
          - toReal (PolyZonotope.mulGDown S₁ S₂ i l))
            * Real.PolyZonotope.monomial (PolyZonotope.mulE S₁ S₂ hp) a l)
      ∈ (PolyZonotope.generatorError (PolyZonotope.mulGDiff S₁ S₂)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.aux_mulG_close S₁ S₂) ha
  -- counts ascribed: through the projection they agree only after unfolding `mul`
  refine ⟨fun i => toReal ((PolyZonotope.mul S₁ S₂ hp).c i)
            + (∑ l : Fin ((S₁.h + 1) * (S₂.h + 1)), toReal (PolyZonotope.mulGDown S₁ S₂ i l)
                * Real.PolyZonotope.monomial (PolyZonotope.mulE S₁ S₂ hp) a l)
            + ∑ j : Fin 0, toReal ((PolyZonotope.mul S₁ S₂ hp).GI i j) * b j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, b, ha, hb, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- binders ascribed: the two layers' counts are one number but not the term `rw` matches
  have hsum : (∑ l : Fin ((S₁.h + 1) * (S₂.h + 1)), toReal (PolyZonotope.mulGDown S₁ S₂ i l)
        * Real.PolyZonotope.monomial (PolyZonotope.mulE S₁ S₂ hp) a l)
      + (∑ l : Fin ((S₁.h + 1) * (S₂.h + 1)),
          (Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
            - toReal (PolyZonotope.mulGDown S₁ S₂ i l))
              * Real.PolyZonotope.monomial (PolyZonotope.mulE S₁ S₂ hp) a l)
      = ∑ l : Fin ((S₁.h + 1) * (S₂.h + 1)),
          Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
            * Real.PolyZonotope.monomial (PolyZonotope.mulE S₁ S₂ hp) a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Pi.add_apply, PolyZonotope.mul, toReal_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  rw [hx i]
  simp only [Real.PolyZonotope.mul, Pi.zero_apply, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  exact hsum

-- the exact statement, read through the refinement: the same image, rounded outward
theorem PolyZonotope.mul_outer (S₁ S₂ : PolyZonotope 𝕋 n) (hp : S₁.p = S₂.p) :
    (fun a : Fin S₁.p → ℝ => Real.PolyZonotope.point (nominal S₁) a
        * Real.PolyZonotope.point (nominal S₂) (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      ⊆ (PolyZonotope.mul S₁ S₂ hp).construct :=
  subset_trans (Real.PolyZonotope.mul_exact (nominal S₁) (nominal S₂) hp).subset
    (PolyZonotope.aux_mul_refines S₁ S₂ hp)

end CORALean.Float
