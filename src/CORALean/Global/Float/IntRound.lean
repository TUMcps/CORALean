import CORALean.Global.Float.SoundFloatArithmetic

/-!
# An integer, enclosed

`intDown a ≤ a ≤ intUp a`: a non-negative integer is `nsmulUp`/`nsmulDown` of one, a negative
one the negation of the opposite rounding of its absolute value. Exact for every integer a
scalar represents, an enclosure otherwise.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The integer `a` from below. -/
def intDown (a : ℤ) : 𝕋 :=
  if 0 ≤ a then nsmulDown a.toNat one else neg (nsmulUp (-a).toNat one)

/-- The integer `a` from above. -/
def intUp (a : ℤ) : 𝕋 :=
  if 0 ≤ a then nsmulUp a.toNat one else neg (nsmulDown (-a).toNat one)

theorem intDown_le_intUp [SoundFloatArithmetic 𝕋] (a : ℤ) :
    toReal (intDown a : 𝕋) ≤ a ∧ (a : ℝ) ≤ toReal (intUp a : 𝕋) := by -- --- PROOF ---
  by_cases h : 0 ≤ a
  · have h1 := nsmulDown_le a.toNat (one : 𝕋)
    have h2 := le_nsmulUp a.toNat (one : 𝕋)
    rw [toReal_one] at h1 h2
    have hc : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    rw [mul_one, hc] at h1 h2
    simp only [intDown, intUp, if_pos h]
    exact ⟨h1, h2⟩
  · have h1 := nsmulDown_le (-a).toNat (one : 𝕋)
    have h2 := le_nsmulUp (-a).toNat (one : 𝕋)
    rw [toReal_one] at h1 h2
    have hc : (((-a).toNat : ℕ) : ℝ) = -(a : ℝ) := by
      have : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
      have h3 : ((((-a).toNat : ℕ) : ℤ) : ℝ) = ((-a : ℤ) : ℝ) := by rw [this]
      push_cast at h3
      exact h3
    rw [mul_one, hc] at h1 h2
    simp only [intDown, intUp, if_neg h, toReal_neg]
    exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
