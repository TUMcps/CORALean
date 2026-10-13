import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
import CORALean.ContSet.PolyZonotope.Float.Theorems.BilinRefines
import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalSetCartProd
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact

/-!
# `PolyZonotope.quadMapMixed` over-approximates the pairwise image

Every pair `(x₁, x₂)` of the two sets lies, appended, in the nominal part of the product of the
two dependent forms (`dependent_nominal`, then the product's nominal part as the append of the
two). The mixed form read at an appended pair is `x₁ᵀ Q x₂`, so the image is the exact layer's
`quadMapDep` of that nominal product (`quadMapDep_exact`), which `bilin_refines` puts inside the
float one. Outer only.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The mixed form at an appended pair is the bilinear form of its blocks. -/
theorem PolyZonotope.aux_mixedForm_eval (Q : Fin m → Mat 𝕋 n n) (x y : Vec ℝ n) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (PolyZonotope.mixedForm Q k)) (Fin.append x y)
      = Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k)) x y := by -- --- PROOF ---
  funext k
  simp only [Real.PolyZonotope.quadEval, Real.PolyZonotope.quadBilin, dotProduct, mulVec,
    PolyZonotope.mixedForm, toRealMat]
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, Fin.append_left,
    Fin.append_right, toReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, zero_add,
    LinearMap.mk₂_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.quadMapMixed_outer (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (fun x : Vec ℝ n × Vec ℝ n => Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k)) x.1 x.2)
        '' (pZ₁.construct ×ˢ pZ₂.construct)
      ⊆ (PolyZonotope.quadMapMixed Q pZ₁ pZ₂).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  -- the pair, appended, is a nominal point of the product of the dependent forms
  have hz : (Fin.append x y : Vec ℝ (n + n)) ∈
      InflatedContSet.nominalSet (pZ₁.dependent.cartProd pZ₂.dependent) := by
    rw [PolyZonotope.nominalSet_cartProd]
    exact ⟨(x, y), ⟨PolyZonotope.dependent_nominal pZ₁ hx, PolyZonotope.dependent_nominal pZ₂ hy⟩,
      rfl⟩
  -- the exact layer's quadratic map of that nominal part, then the float refinement
  have hq := (Real.PolyZonotope.quadMapDep_exact
    (fun k => toRealMat (PolyZonotope.mixedForm Q k))
    (nominal (pZ₁.dependent.cartProd pZ₂.dependent)) rfl).subset ⟨_, hz, rfl⟩
  rw [PolyZonotope.aux_mixedForm_eval] at hq
  exact PolyZonotope.bilin_refines (PolyZonotope.mixedForm Q) _ _ rfl hq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
