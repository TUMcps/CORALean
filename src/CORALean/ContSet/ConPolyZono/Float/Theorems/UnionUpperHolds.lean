import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperA
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperB
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionConIntEq
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsUnionUpperIff
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# The stored selector rows hold wherever the exact ones do

At a factor vector in the cube, the exact layer's two selector rows hold. The first is
copied. The second is stored scaled to integers and rounded: its value moves by at most the
sum of the coefficients' rounding gaps, a monomial being at most `1`, and `unionConErr` is
that sum rounded up, which is the bound the stored row is held to.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored row's value is within the summed gaps of the integer row's. -/
theorem ConPolyZono.aux_unionCon_close (p₁ p₂ : ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ)
    (ha : ∀ k, |a k| ≤ 1) :
    |(∑ l, toReal (ConPolyZono.unionConCoef p₁ p₂ l : 𝕋)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k)
      - ∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k|
      ≤ toReal (ConPolyZono.unionConErr p₁ p₂ : 𝕋) := by -- --- PROOF ---
  have hgap : ∀ l, |(toReal (ConPolyZono.unionConCoef p₁ p₂ l : 𝕋)
        - (ConPolyZono.unionConInt p₁ p₂ l : ℝ))|
      ≤ toReal (subUp (intUp (ConPolyZono.unionConInt p₁ p₂ l))
        (intDown (ConPolyZono.unionConInt p₁ p₂ l)) : 𝕋) := fun l => by
    obtain ⟨h1, h2⟩ := intDown_le_intUp (𝕋 := 𝕋) (ConPolyZono.unionConInt p₁ p₂ l)
    have h3 := sub_le_subUp (intUp (ConPolyZono.unionConInt p₁ p₂ l) : 𝕋)
      (intDown (ConPolyZono.unionConInt p₁ p₂ l))
    rw [abs_le]
    constructor <;> simp only [ConPolyZono.unionConCoef] <;> linarith
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun l _ => ?_)
    (sum_le_sumUp _))
  rw [← sub_mul, abs_mul]
  exact le_trans (mul_le_of_le_one_right (abs_nonneg _)
    (Real.PolyZonotope.abs_monomial_le_one
      (fun k l => Real.ConPolyZono.unionConCol p₁ p₂ l k) ha l))
    (hgap l)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.holds_unionUpper_of_real (p₁ p₂ : ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ)
    (ha : ∀ k, |a k| ≤ 1)
    (h : Real.ConPolyZono.holds (Real.ConPolyZono.unionUpperA p₁ p₂)
      Real.ConPolyZono.unionUpperB (Real.ConPolyZono.unionUpperEC p₁ p₂) a) :
    Real.ConPolyZono.holds (toRealMat (ConPolyZono.unionUpperA p₁ p₂ : Mat 𝕋 _ _))
      (ConPolyZono.unionUpperB p₁ p₂ : Interval (Vec 𝕋 _)).nominal
      (Real.ConPolyZono.unionUpperEC p₁ p₂) a := by -- --- PROOF ---
  rw [ConPolyZono.unionUpperA, ConPolyZono.unionUpperB, ConPolyZono.toRealMat_plusA,
    ConPolyZono.nominal_plusB, Real.ConPolyZono.unionUpperEC, Real.ConPolyZono.holds_shared_iff]
  rw [Real.ConPolyZono.unionUpperA, Real.ConPolyZono.unionUpperB, Real.ConPolyZono.unionUpperEC,
    Real.ConPolyZono.holds_shared_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · -- the `α₁α₂ = 1` row is copied, its entry `one` reading back as `1`
    have hA : toRealMat (fun (_ : Fin 1) (_ : Fin 1) => (one : 𝕋)) = fun _ _ => 1 :=
      funext fun _ => funext fun _ => toReal_one
    have hb : (⟨fun _ : Fin 1 => (one : 𝕋), fun _ => one⟩ : Interval (Vec 𝕋 1)).nominal
        = Real.Interval.point (fun _ => (1 : ℝ)) := by
      simp only [Interval.nominal, RealImage.realImage, Real.Interval.point]
      congr 1 <;> funext _ <;> exact toReal_one
    rw [hA, hb]
    exact h₁
  · -- the selector row: the integer row's value is zero, the stored one within `unionConErr`
    have h0 := h₂ i
    simp only [Real.Interval.point, Matrix.mulVec, dotProduct, Real.PolyZonotope.monomial,
      Pi.zero_apply] at h0
    -- the integer row's value is the exact row's, scaled, hence zero
    have hz : (∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
        * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k) = 0 := by
      have hs : (∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k)
          = (4 * ((max 1 p₁ : ℕ) : ℝ) * ((max 1 p₂ : ℕ) : ℝ))
            * ∑ l, Real.ConPolyZono.unionConCoef p₁ p₂ l
              * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by
          rw [← ConPolyZono.unionConInt_eq, mul_assoc]
      rw [hs, le_antisymm h0.2 h0.1, mul_zero]
    -- the stored row is within `unionConErr` of it
    have hc := ConPolyZono.aux_unionCon_close (𝕋 := 𝕋) p₁ p₂ a ha
    rw [hz, sub_zero, abs_le] at hc
    refine ⟨?_, ?_⟩
    · simp only [Interval.nominal, RealImage.realImage, toRealVec, toReal_neg, Matrix.mulVec,
        dotProduct, Real.PolyZonotope.monomial, toRealMat]
      linarith [hc.1]
    · simp only [Interval.nominal, RealImage.realImage, toRealVec, Matrix.mulVec, dotProduct,
        Real.PolyZonotope.monomial, toRealMat]
      linarith [hc.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
