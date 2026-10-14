module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerR

@[expose] public section

/-!
# The stored operand rows hold wherever the exact ones do

Read back, the stored lower constraint matrix is the exact layer's: copying, halving and
negation round nothing. Only the upper bounds differ, `b.sup - b.inf / 2` being rounded up, so
every row the exact system satisfies the stored one satisfies too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Read back, the stored matrix is the exact layer's on the read-back operands. -/
theorem ConPolyZono.aux_toRealMat_unionLowerA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁)
    (b₁ : Interval (Vec 𝕋 m₁)) (A₂ : Mat 𝕋 m₂ q₂) (b₂ : Interval (Vec 𝕋 m₂)) :
    toRealMat (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂)
      = Real.ConPolyZono.unionLowerA (toRealMat A₁) b₁.nominal (toRealMat A₂)
        b₂.nominal := by -- --- PROOF ---
  funext i l
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · have := congrFun (congrFun (ConPolyZono.toRealMat_plusA A₁ A₂) i) l
    simpa only [toRealMat, ConPolyZono.unionLowerA, Real.ConPolyZono.unionLowerA,
      Fin.append_left] using this
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
      simp only [toRealMat, ConPolyZono.unionLowerA, Real.ConPolyZono.unionLowerA,
        Fin.append_right, Fin.append_left, toReal_neg, toReal_half, Interval.nominal,
        RealImage.realImage, toRealVec] <;> ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.holds_unionLower_of_real {p₁ p₂ m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁)
    (b₁ : Interval (Vec 𝕋 m₁)) (A₂ : Mat 𝕋 m₂ q₂) (b₂ : Interval (Vec 𝕋 m₂))
    (R₁ : Fin p₁ → Fin q₁ → ℕ) (R₂ : Fin p₂ → Fin q₂ → ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ)
    (h : Real.ConPolyZono.holds
      (Real.ConPolyZono.unionLowerA (toRealMat A₁) b₁.nominal (toRealMat A₂) b₂.nominal)
      (Real.ConPolyZono.unionLowerB b₁.nominal b₂.nominal)
      (Real.ConPolyZono.unionLowerR R₁ R₂) a) :
    Real.ConPolyZono.holds (toRealMat (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂))
      (ConPolyZono.unionLowerB b₁ b₂).nominal (Real.ConPolyZono.unionLowerR R₁ R₂)
        a := by -- --- PROOF ---
  -- the matrix is the exact one, so only the bounds are left
  rw [ConPolyZono.aux_toRealMat_unionLowerA]
  intro i
  obtain ⟨h1, h2⟩ := h i
  refine ⟨?_, ?_⟩
  · refine le_trans (le_of_eq ?_) h1
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
      simp only [ConPolyZono.unionLowerB, Real.ConPolyZono.unionLowerB, Interval.nominal,
        RealImage.realImage, toRealVec, Fin.append_left, Fin.append_right, toReal_half] <;> ring
  · refine le_trans h2 ?_
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · have := sub_le_subUp (b₁.sup r) (half (b₁.inf r))
      simp only [ConPolyZono.unionLowerB, Real.ConPolyZono.unionLowerB, Interval.nominal,
        RealImage.realImage, toRealVec, Fin.append_left, toReal_half] at this ⊢
      linarith
    · have := sub_le_subUp (b₂.sup r) (half (b₂.inf r))
      simp only [ConPolyZono.unionLowerB, Real.ConPolyZono.unionLowerB, Interval.nominal,
        RealImage.realImage, toRealVec, Fin.append_right, toReal_half] at this ⊢
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
