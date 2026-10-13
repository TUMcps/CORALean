import CORALean.ContSet.Ellipsoid.Float.Operations.Isequal

/-!
# `Ellipsoid.isequal` is sound

A `true` answer says the stored centres, generators and error boxes agree as real numbers, so the
nominal ellipsoids are the same and the error boxes are the same, and the denoted sets are equal.
`false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isequal_sound {E S : Ellipsoid 𝕋 n} (h : E.isequal S = true) :
    E.construct = S.construct := by -- --- PROOF ---
  unfold Ellipsoid.isequal at h
  split at h
  · rename_i e
    simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, forall_const] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨k₁, q₁, G₁, E₁⟩ := E
    obtain ⟨k₂, q₂, G₂, E₂⟩ := S
    simp only at e
    subst e
    have hq : toRealVec q₁ = toRealVec q₂ := funext fun i => eqr (h i).1.1.1
    have hG : toRealMat G₁ = toRealMat G₂ :=
      funext fun i => funext fun j => eqr (by simpa using (h i).2 j)
    have hEi : toRealVec E₁.inf = toRealVec E₂.inf := funext fun i => eqr (h i).1.1.2
    have hEs : toRealVec E₁.sup = toRealVec E₂.sup := funext fun i => eqr (h i).1.2
    -- the error boxes read as the same real box
    have hE : E₁.construct = E₂.construct := by
      have : E₁.nominal = E₂.nominal := by
        have e₁ : RealImage.realImage E₁.inf = RealImage.realImage E₂.inf := hEi
        have e₂ : RealImage.realImage E₁.sup = RealImage.realImage E₂.sup := hEs
        simp only [Interval.nominal, e₁, e₂]
      unfold Interval.construct
      rw [this]
    have hN : (nominal (⟨k₁, q₁, G₁, E₁⟩ : Ellipsoid 𝕋 n)) =
        nominal (⟨k₁, q₂, G₂, E₂⟩ : Ellipsoid 𝕋 n) := by
      show (⟨k₁, toRealVec q₁, toRealMat G₁⟩ : CORALean.Real.Ellipsoid n) =
        ⟨k₁, toRealVec q₂, toRealMat G₂⟩
      rw [hq, hG]
    -- so the two sums of nominal set and error box are the same
    change ContSet.construct (nominal (⟨k₁, q₁, G₁, E₁⟩ : Ellipsoid 𝕋 n)) + E₁.construct =
      ContSet.construct (nominal (⟨k₁, q₂, G₂, E₂⟩ : Ellipsoid 𝕋 n)) + E₂.construct
    rw [hN, hE]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
