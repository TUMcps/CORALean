import CORALean.ContSet.PolyZonotope.Float.Operations.Isequal

/-!
# `PolyZonotope.isequal` is sound

A `true` answer says the stored numbers agree as real numbers and the exponent matrices agree, so
the nominal polynomial zonotopes are the same and the error boxes are the same, and the denoted
sets are equal. `false` refutes nothing.
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

theorem PolyZonotope.isequal_sound {Z S : PolyZonotope (Vec 𝕋 n)} (h : Z.isequal S = true) :
    Z.construct = S.construct := by -- --- PROOF ---
  unfold PolyZonotope.isequal at h
  split at h
  · rename_i e
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
      beq_iff_eq] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨hnum, hE⟩ := h
    obtain ⟨p₁, h₁, q₁, c₁, G₁, E₁, GI₁, r₁⟩ := Z
    obtain ⟨p₂, h₂, q₂, c₂, G₂, E₂, GI₂, r₂⟩ := S
    simp only at e hnum hE
    obtain ⟨rfl, rfl, rfl⟩ := e
    simp only [Fin.cast_eq_self] at hnum hE
    have hc : toRealVec c₁ = toRealVec c₂ := funext fun i => eqr (hnum i).1.1.1.1
    have hG : (fun l i => toReal (G₁ l i)) = fun l i => toReal (G₂ l i) :=
      funext fun l => funext fun i => eqr (by simpa using (hnum i).1.2 l)
    have hGI : (fun l i => toReal (GI₁ l i)) = fun l i => toReal (GI₂ l i) :=
      funext fun l => funext fun i => eqr (by simpa using (hnum i).2 l)
    have hEi : toRealVec r₁.inf = toRealVec r₂.inf := funext fun i => eqr (hnum i).1.1.1.2
    have hEs : toRealVec r₁.sup = toRealVec r₂.sup := funext fun i => eqr (hnum i).1.1.2
    have hE' : E₁ = E₂ := funext fun k => funext fun j => hE k j
    -- the error boxes read as the same real box
    have hr : r₁.construct = r₂.construct := by
      have : r₁.nominal = r₂.nominal := by
        have e₁ : RealImage.realImage r₁.inf = RealImage.realImage r₂.inf := hEi
        have e₂ : RealImage.realImage r₁.sup = RealImage.realImage r₂.sup := hEs
        simp only [Interval.nominal, e₁, e₂]
      unfold Interval.construct
      rw [this]
    -- the nominal sets agree field by field
    have hN : (nominal (⟨p₁, h₁, q₁, c₁, G₁, E₁, GI₁, r₁⟩ : PolyZonotope (Vec 𝕋 n))) =
        nominal (⟨p₁, h₁, q₁, c₂, G₂, E₂, GI₂, r₂⟩ : PolyZonotope (Vec 𝕋 n)) := by
      show (⟨p₁, h₁, q₁, toRealVec c₁, fun l i => toReal (G₁ l i), E₁,
          fun j i => toReal (GI₁ j i)⟩ : CORALean.Real.PolyZonotope (Vec ℝ n)) =
        ⟨p₁, h₁, q₁, toRealVec c₂, fun l i => toReal (G₂ l i), E₂, fun j i => toReal (GI₂ j i)⟩
      rw [hc, hG, hGI, hE']
    change ContSet.construct
      (nominal (⟨p₁, h₁, q₁, c₁, G₁, E₁, GI₁, r₁⟩ : PolyZonotope (Vec 𝕋 n))) +
        r₁.construct =
      ContSet.construct (nominal (⟨p₁, h₁, q₁, c₂, G₂, E₂, GI₂, r₂⟩ : PolyZonotope (Vec 𝕋 n))) +
        r₂.construct
    rw [hN, hr]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
