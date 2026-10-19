module

public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreCartProd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCartProd
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# What `PolyLevelSet.cartProd` denotes over a floating-point scalar

The product of the two sets: the product's rows read back as the exact product's
(`eval_nominalCore_cartProd`), whose values are each operand's at its own variables
(`Real.PolyLevelSet.eval_cartProd`), and the slacks are stacked alike.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the product is a point of each operand, on its own block of variables. -/
theorem PolyLevelSet.mem_cartProd_iff (P₁ : PolyLevelSet 𝕋 n₁) (P₂ : PolyLevelSet 𝕋 n₂)
    (x : Vec ℝ (n₁ + n₂)) : -- --- STMT ---
    x ∈ (P₁.cartProd P₂).construct
      ↔ (fun k => x (Fin.castAdd n₂ k)) ∈ P₁.construct
        ∧ (fun k => x (Fin.natAdd n₁ k)) ∈ P₂.construct := by -- --- PROOF ---
  show (∀ i : Fin (P₁.m + P₂.m), ((P₁.cartProd P₂).op i).IsMetWithin
    ((P₁.cartProd P₂).nominalCore.eval x i) |toReal ((P₁.cartProd P₂).b_error i)|) ↔ _
  rw [PolyLevelSet.eval_nominalCore_cartProd, Real.PolyLevelSet.eval_cartProd,
      Real.LevelSet.forall_fin_add]
  simp only [PolyLevelSet.cartProd, Fin.append_left, Fin.append_right]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
