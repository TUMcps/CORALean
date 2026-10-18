module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CartProd
public import CORALean.Global.Float.GenBlockDiag
public import CORALean.ContSet.ConPolyZono.Real.Theorems.RelaxCartProd
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecPlusB
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

@[expose] public section

/-!
# `ConPolyZono.cartProd` is exact

The stored operands' sets, paired and read through `Fin.append`, are the product's set. Nothing
rounds: the stored product read back is the exact layer's `cartProd` mapped through the append,
field by field, its slacks the two side by side, so its nominal part is the product of the two
relaxed operands (`relax_cartProd`); the error box is the stack of the two.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_realG_left (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂))
    (l : Fin cPZ₁.h) : -- --- STMT ---
    (Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).G
      (Fin.castAdd cPZ₂.h l) = (cPZ₁.nominalCore.G l, 0) := by -- --- PROOF ---
  dsimp only [Real.ConPolyZono.cartProd]
  exact Fin.append_left (m := cPZ₁.h) (n := cPZ₂.h) _ _ l

theorem ConPolyZono.aux_realG_right (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂))
    (l : Fin cPZ₂.h) : -- --- STMT ---
    (Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).G
      (Fin.natAdd cPZ₁.h l) = (0, cPZ₂.nominalCore.G l) := by -- --- PROOF ---
  dsimp only [Real.ConPolyZono.cartProd]
  exact Fin.append_right (m := cPZ₁.h) (n := cPZ₂.h) _ _ l

-- the same for the independent generators
theorem ConPolyZono.aux_realGI_left (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂))
    (l : Fin cPZ₁.qI) : -- --- STMT ---
    (Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).GI
      (Fin.castAdd cPZ₂.qI l) = (cPZ₁.nominalCore.GI l, 0) := by -- --- PROOF ---
  dsimp only [Real.ConPolyZono.cartProd]
  exact Fin.append_left (m := cPZ₁.qI) (n := cPZ₂.qI) _ _ l

theorem ConPolyZono.aux_realGI_right (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂))
    (l : Fin cPZ₂.qI) : -- --- STMT ---
    (Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).GI
      (Fin.natAdd cPZ₁.qI l) = (0, cPZ₂.nominalCore.GI l) := by -- --- PROOF ---
  dsimp only [Real.ConPolyZono.cartProd]
  exact Fin.append_right (m := cPZ₁.qI) (n := cPZ₂.qI) _ _ l

/-- The nominal constrained polynomial zonotope of the product is the exact product of the
read-back operands, relaxed by their slacks side by side, mapped through the append. -/
theorem ConPolyZono.aux_nominal_cartProd (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂)) : -- --- STMT ---
    InflatedContSet.nominal (cPZ₁.cartProd cPZ₂) =
      Real.ConPolyZono.map (appendLinear n₁ n₂)
        ((Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).relax
          (Fin.append (toRealVec cPZ₁.b_error) (toRealVec cPZ₂.b_error))) := by -- --- PROOF ---
  show (⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ : Real.ConPolyZono (Vec ℝ (n₁ + n₂))) =
    ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  congr 1
  · -- the centers
    rw [appendLinear_apply]
    exact toRealVec_append cPZ₁.c cPZ₂.c
  · -- the dependent generators, column by column
    funext l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · show (fun i => toReal (genBlockDiag (fun i l => cPZ₁.G l i) (fun i l => cPZ₂.G l i) i
        (Fin.castAdd cPZ₂.h l))) = (appendLinear n₁ n₂)
          ((Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).G (Fin.castAdd cPZ₂.h l))
      rw [toReal_genBlockDiag_left, ConPolyZono.aux_realG_left, appendLinear_apply]
      rfl
    · show (fun i => toReal (genBlockDiag (fun i l => cPZ₁.G l i) (fun i l => cPZ₂.G l i) i
        (Fin.natAdd cPZ₁.h l))) = (appendLinear n₁ n₂)
          ((Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).G (Fin.natAdd cPZ₁.h l))
      rw [toReal_genBlockDiag_right, ConPolyZono.aux_realG_right, appendLinear_apply]
      rfl
  · -- the independent generators, column by column
    funext l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · show (fun i => toReal (genBlockDiag (fun i j => cPZ₁.GI j i) (fun i j => cPZ₂.GI j i) i
        (Fin.castAdd cPZ₂.qI l))) = (appendLinear n₁ n₂)
          ((Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).GI (Fin.castAdd cPZ₂.qI l))
      rw [toReal_genBlockDiag_left, ConPolyZono.aux_realGI_left, appendLinear_apply]
      rfl
    · show (fun i => toReal (genBlockDiag (fun i j => cPZ₁.GI j i) (fun i j => cPZ₂.GI j i) i
        (Fin.natAdd cPZ₁.qI l))) = (appendLinear n₁ n₂)
          ((Real.ConPolyZono.cartProd cPZ₁.nominalCore cPZ₂.nominalCore).GI (Fin.natAdd cPZ₁.qI l))
      rw [toReal_genBlockDiag_right, ConPolyZono.aux_realGI_right, appendLinear_apply]
      rfl
  · -- the constraint matrix, with the slack columns
    funext i
    have hA := ConPolyZono.toRealMat_plusA cPZ₁.A cPZ₂.A
    have hs := ConPolyZono.toRealVec_plusB cPZ₁.b_error cPZ₂.b_error
    show Fin.append (toRealMat (ConPolyZono.plusA cPZ₁.A cPZ₂.A) i)
        (Pi.single i (toRealVec (ConPolyZono.plusB cPZ₁.b_error cPZ₂.b_error) i))
      = Fin.append (Real.ConPolyZono.plusA (toRealMat cPZ₁.A) (toRealMat cPZ₂.A) i)
        (Pi.single i (Fin.append (toRealVec cPZ₁.b_error) (toRealVec cPZ₂.b_error) i))
    rw [hA, hs]
    rfl
  · -- the right-hand sides
    exact ConPolyZono.toRealVec_plusB _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.cartProd_exact (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁))
    (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂)) :
    (cPZ₁.cartProd cPZ₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (cPZ₁.construct ×ˢ cPZ₂.construct) := by -- --- PROOF ---
  -- the nominal part: the exact product, mapped through the append
  have hN : InflatedContSet.nominalSet (cPZ₁.cartProd cPZ₂) =
      (appendLinear n₁ n₂) ''
        (InflatedContSet.nominalSet cPZ₁ ×ˢ InflatedContSet.nominalSet cPZ₂) := by
    unfold InflatedContSet.nominalSet
    rw [ConPolyZono.aux_nominal_cartProd]
    show (Real.ConPolyZono.map _ _).construct = _ ''
      (Real.ConPolyZono.construct _ ×ˢ Real.ConPolyZono.construct _)
    rw [← Real.ConPolyZono.map_exact, Real.ConPolyZono.relax_cartProd]
    rfl
  have hφ : ⇑(appendLinear n₁ n₂) = fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2 :=
    funext appendLinear_apply
  rw [hφ] at hN
  -- the error box is the stack of the two, and stacking distributes over the sum
  exact CORALean.Float.InflatedContSet.append_construct (s₁ := cPZ₁) (s₂ := cPZ₂) hN rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
