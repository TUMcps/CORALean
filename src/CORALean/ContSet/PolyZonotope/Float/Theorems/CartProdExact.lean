import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
import CORALean.Global.Float.GenBlockDiag
import CORALean.ContSet.PolyZonotope.Real.Theorems.CartProdExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

/-!
# `PolyZonotope.cartProd` is exact

The stored operands' sets, paired and read through `Fin.append`, are the product's set. Nothing
rounds: the nominal part is the exact layer's `cartProd` mapped through the append, field by
field, and the error box is the stack of the two.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_realG_left (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂)
    (l : Fin pZ₁.h) :
    (Real.PolyZonotope.cartProd (InflatedContSet.nominal pZ₁) (InflatedContSet.nominal pZ₂)).G
      (Fin.castAdd pZ₂.h l) = ((InflatedContSet.nominal pZ₁).G l, 0) := by
  dsimp only [Real.PolyZonotope.cartProd]
  exact Fin.append_left (m := pZ₁.h) (n := pZ₂.h) _ _ l

theorem PolyZonotope.aux_realG_right (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂)
    (l : Fin pZ₂.h) :
    (Real.PolyZonotope.cartProd (InflatedContSet.nominal pZ₁) (InflatedContSet.nominal pZ₂)).G
      (Fin.natAdd pZ₁.h l) = (0, (InflatedContSet.nominal pZ₂).G l) := by
  dsimp only [Real.PolyZonotope.cartProd]
  exact Fin.append_right (m := pZ₁.h) (n := pZ₂.h) _ _ l

theorem PolyZonotope.aux_realGI_left (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂)
    (l : Fin pZ₁.q) :
    (Real.PolyZonotope.cartProd (InflatedContSet.nominal pZ₁) (InflatedContSet.nominal pZ₂)).GI
      (Fin.castAdd pZ₂.q l) = ((InflatedContSet.nominal pZ₁).GI l, 0) := by
  dsimp only [Real.PolyZonotope.cartProd]
  exact Fin.append_left (m := pZ₁.q) (n := pZ₂.q) _ _ l

theorem PolyZonotope.aux_realGI_right (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂)
    (l : Fin pZ₂.q) :
    (Real.PolyZonotope.cartProd (InflatedContSet.nominal pZ₁) (InflatedContSet.nominal pZ₂)).GI
      (Fin.natAdd pZ₁.q l) = (0, (InflatedContSet.nominal pZ₂).GI l) := by
  dsimp only [Real.PolyZonotope.cartProd]
  exact Fin.append_right (m := pZ₁.q) (n := pZ₂.q) _ _ l

/-- The nominal polynomial zonotope of the product is the exact product, mapped through the
append. -/
theorem PolyZonotope.aux_nominal_cartProd (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂) :
    InflatedContSet.nominal (pZ₁.cartProd pZ₂) =
      Real.PolyZonotope.map (appendLinear n₁ n₂)
        (Real.PolyZonotope.cartProd (InflatedContSet.nominal pZ₁)
          (InflatedContSet.nominal pZ₂)) := by -- --- PROOF ---
  show (⟨_, _, _, _, _, _, _⟩ : Real.PolyZonotope (Vec ℝ (n₁ + n₂))) = ⟨_, _, _, _, _, _, _⟩
  congr 1
  · -- the centres
    rw [appendLinear_apply]
    exact toRealVec_append pZ₁.c pZ₂.c
  · -- the dependent generators, column by column
    funext l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · show (fun i => toReal (genBlockDiag pZ₁.G pZ₂.G i (Fin.castAdd pZ₂.h l))) = _
      rw [toReal_genBlockDiag_left, PolyZonotope.aux_realG_left, appendLinear_apply]
      rfl
    · show (fun i => toReal (genBlockDiag pZ₁.G pZ₂.G i (Fin.natAdd pZ₁.h l))) = _
      rw [toReal_genBlockDiag_right, PolyZonotope.aux_realG_right, appendLinear_apply]
      rfl
  · -- the independent generators, column by column
    funext l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · show (fun i => toReal (genBlockDiag pZ₁.GI pZ₂.GI i (Fin.castAdd pZ₂.q l))) = _
      rw [toReal_genBlockDiag_left, PolyZonotope.aux_realGI_left, appendLinear_apply]
      rfl
    · show (fun i => toReal (genBlockDiag pZ₁.GI pZ₂.GI i (Fin.natAdd pZ₁.q l))) = _
      rw [toReal_genBlockDiag_right, PolyZonotope.aux_realGI_right, appendLinear_apply]
      rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cartProd_exact (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂) :
    (pZ₁.cartProd pZ₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (pZ₁.construct ×ˢ pZ₂.construct) := by -- --- PROOF ---
  -- the nominal part: the exact product, mapped through the append
  have hN : InflatedContSet.nominalSet (pZ₁.cartProd pZ₂) =
      (appendLinear n₁ n₂) ''
        (InflatedContSet.nominalSet pZ₁ ×ˢ InflatedContSet.nominalSet pZ₂) := by
    unfold InflatedContSet.nominalSet
    rw [PolyZonotope.aux_nominal_cartProd]
    show (Real.PolyZonotope.map _ _).construct = _ ''
      (Real.PolyZonotope.construct _ ×ˢ Real.PolyZonotope.construct _)
    rw [← Real.PolyZonotope.map_exact, Real.PolyZonotope.cartProd_exact]
  have hφ : ⇑(appendLinear n₁ n₂) = fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2 :=
    funext appendLinear_apply
  rw [hφ] at hN
  -- the error box is the stack of the two, and stacking distributes over the sum
  exact CORALean.Float.InflatedContSet.append_construct (s₁ := pZ₁) (s₂ := pZ₂) hN rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
