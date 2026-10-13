import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulGClose
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact

/-!
# `PolyZonotope.mul` encloses the exact product over shared factors

The exact layer proves what the operation is — the image of the shared factors
under `a ↦ point pZ₁ a ⊙ point pZ₂ a` — and this file adds only what rounding
costs. The input is the two nominal sets: `mul` is an operation on sets whose
independent block and error box `dependent` has already emptied, and from there
the two layers differ in their generator entries alone, which `generatorError`
prices exactly as it does for `mtimes` and `quadMap`.

`mulG_close` prices one entry; the whole difference from `quadMap` is that a
rounded product needs nothing bracketed in between, where `quadMap`'s bilinear
form has to carry its middle vector as an interval.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## The refinement -/


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_mul_refines (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (hp : pZ₁.p = pZ₂.p) :
    (Real.PolyZonotope.mul (nominal pZ₁) (nominal pZ₂) hp).construct
      ⊆ (PolyZonotope.mul pZ₁ pZ₂ hp).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, b, ha, hb, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  have hbox : (fun i => ∑ l,
        (Real.PolyZonotope.mulG (nominal pZ₁) (nominal pZ₂) l i
          - toReal (PolyZonotope.mulGDown pZ₁ pZ₂ i l))
            * Real.PolyZonotope.monomial (PolyZonotope.mulE pZ₁ pZ₂ hp) a l)
      ∈ (PolyZonotope.generatorError (PolyZonotope.mulGDiff pZ₁ pZ₂)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.mulG_close pZ₁ pZ₂) ha
  -- counts ascribed: through the projection they agree only after unfolding `mul`
  refine ⟨fun i => toReal ((PolyZonotope.mul pZ₁ pZ₂ hp).c i)
            + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)), toReal (PolyZonotope.mulGDown pZ₁ pZ₂ i l)
                * Real.PolyZonotope.monomial (PolyZonotope.mulE pZ₁ pZ₂ hp) a l)
            + ∑ j : Fin 0, toReal ((PolyZonotope.mul pZ₁ pZ₂ hp).GI j i) * b j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, b, ha, hb, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- binders ascribed: the two layers' counts are one number but not the term `rw` matches
  have hsum : (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)), toReal (PolyZonotope.mulGDown pZ₁ pZ₂ i l)
        * Real.PolyZonotope.monomial (PolyZonotope.mulE pZ₁ pZ₂ hp) a l)
      + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
          (Real.PolyZonotope.mulG (nominal pZ₁) (nominal pZ₂) l i
            - toReal (PolyZonotope.mulGDown pZ₁ pZ₂ i l))
              * Real.PolyZonotope.monomial (PolyZonotope.mulE pZ₁ pZ₂ hp) a l)
      = ∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
          Real.PolyZonotope.mulG (nominal pZ₁) (nominal pZ₂) l i
            * Real.PolyZonotope.monomial (PolyZonotope.mulE pZ₁ pZ₂ hp) a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Pi.add_apply, PolyZonotope.mul, toReal_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  rw [hx i]
  simp only [Real.PolyZonotope.mul, Pi.zero_apply, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero, zero_add]
  exact hsum


-- =======================================  MAIN THEOREM  ======================================= --

-- the exact statement, read through the refinement: the same image, rounded outward
theorem PolyZonotope.mul_outer (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (hp : pZ₁.p = pZ₂.p) :
    (fun a : Fin pZ₁.p → ℝ => Real.PolyZonotope.point (nominal pZ₁) a
        * Real.PolyZonotope.point (nominal pZ₂) (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      ⊆ (PolyZonotope.mul pZ₁ pZ₂ hp).construct :=
  subset_trans (Real.PolyZonotope.mul_exact (nominal pZ₁) (nominal pZ₂) hp).subset
    (PolyZonotope.aux_mul_refines pZ₁ pZ₂ hp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
