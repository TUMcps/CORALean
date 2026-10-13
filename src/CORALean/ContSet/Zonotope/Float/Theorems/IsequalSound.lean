import CORALean.ContSet.Zonotope.Float.Operations.Isequal
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.isequal` is sound

A `true` answer says the stored centres, generators and error boxes agree as real numbers, so
the nominal zonotopes are the same and the error boxes are the same, and the denoted sets are
equal. `false` refutes nothing.
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

theorem Zonotope.isequal_sound {Z S : Zonotope (Vec 𝕋 n)} (h : Z.isequal S = true) :
    Z.construct = S.construct := by -- --- PROOF ---
  unfold Zonotope.isequal at h
  split at h
  · rename_i e
    simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, forall_const] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨h₁, c₁, G₁, E₁⟩ := Z
    obtain ⟨h₂, c₂, G₂, E₂⟩ := S
    simp only at e
    subst e
    have hc : toRealVec c₁ = toRealVec c₂ := funext fun i => eqr (h i).1.1.1
    have hG : (fun j i => toReal (G₁ j i)) = fun j i => toReal (G₂ j i) :=
      funext fun j => funext fun i => eqr (by simpa using (h i).2 j)
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
    have hN : (nominal (⟨h₁, c₁, G₁, E₁⟩ : Zonotope (Vec 𝕋 n))) =
        nominal (⟨h₁, c₂, G₂, E₂⟩ : Zonotope (Vec 𝕋 n)) := by
      show (⟨h₁, toRealVec c₁, fun j i => toReal (G₁ j i)⟩ : CORALean.Real.Zonotope (Vec ℝ n)) =
        ⟨h₁, toRealVec c₂, fun j i => toReal (G₂ j i)⟩
      rw [hc, hG]
    -- so the two sums of nominal set and error box are the same
    change ContSet.construct (nominal (⟨h₁, c₁, G₁, E₁⟩ : Zonotope (Vec 𝕋 n))) + E₁.construct =
      ContSet.construct (nominal (⟨h₁, c₂, G₂, E₂⟩ : Zonotope (Vec 𝕋 n))) + E₂.construct
    rw [hN, hE]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
