module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA

@[expose] public section

/-!
# The stored operand rows read back to the exact layer's

Read back, the stored lower constraint matrix is the exact layer's on the read-back operands:
copying, halving and negation round nothing, and so does the right-hand side `b / 2`
(`toRealVec_unionLowerB`), so the stored operand rows are the exact ones, slack and all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_toRealMat_plusA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁)
    (A₂ : Mat 𝕋 m₂ q₂) :
    toRealMat (ConPolyZono.plusA A₁ A₂)
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) := by -- --- PROOF ---
  have key : ∀ i l, toRealMat (ConPolyZono.plusA A₁ A₂) i l
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) i l := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) <;>
      simp only [toRealMat, ConPolyZono.plusA, Real.ConPolyZono.plusA,
        Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  exact funext fun i => funext fun l => key i l


-- =======================================  MAIN THEOREM  ======================================= --

/-- Read back, the stored matrix is the exact layer's on the read-back operands. -/
theorem ConPolyZono.toRealMat_unionLowerA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁)
    (b₁ : Vec 𝕋 m₁) (A₂ : Mat 𝕋 m₂ q₂) (b₂ : Vec 𝕋 m₂) : -- --- STMT ---
    toRealMat (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂)
      = Real.ConPolyZono.unionLowerA (toRealMat A₁) (toRealVec b₁) (toRealMat A₂)
        (toRealVec b₂) := by -- --- PROOF ---
  funext i l
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · have := congrFun (congrFun (ConPolyZono.aux_toRealMat_plusA A₁ A₂) i) l
    simpa only [toRealMat, ConPolyZono.unionLowerA, Real.ConPolyZono.unionLowerA,
      Fin.append_left] using this
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
      simp only [toRealMat, ConPolyZono.unionLowerA, Real.ConPolyZono.unionLowerA,
        Fin.append_right, Fin.append_left, toReal_neg, toReal_half, toRealVec] <;> ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
