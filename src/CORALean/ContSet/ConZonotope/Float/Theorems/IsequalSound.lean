module

public import CORALean.ContSet.ConZonotope.Float.Operations.Isequal
public import CORALean.ContSet.HPolytope.Float.Theorems.IsequalNominal

@[expose] public section

/-!
# `ConZonotope.isequal` is sound

A `true` answer says the stored numbers agree as real numbers and the constraint polytopes are
equal, so the nominal sets are the same and the error boxes are the same, and the denoted sets
are equal. `false` refutes nothing.

## Inputs
* `Z` – first constrained zonotope
* `S` – second constrained zonotope

## Hypotheses
* `h` – the test answers true

## Conclusion
* the two sets are equal
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

theorem ConZonotope.isequal_sound {Z S : ConZonotope 𝕋 (Vec 𝕋 n)}
    (h : Z.isequal S = true) : -- --- CONCL ---
    Z.construct = S.construct := by -- --- PROOF ---
  unfold ConZonotope.isequal at h
  split at h
  · rename_i e
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨hnum, hP⟩ := h
    obtain ⟨h₁, c₁, G₁, P₁, E₁⟩ := Z
    obtain ⟨h₂, c₂, G₂, P₂, E₂⟩ := S
    simp only at e hnum hP
    subst e
    simp only [Fin.cast_eq_self] at hnum
    have hc : toRealVec c₁ = toRealVec c₂ := funext fun i => eqr (hnum i).1.1.1
    have hG : (fun j => toRealVec (G₁ j)) = fun j => toRealVec (G₂ j) :=
      funext fun j => funext fun i => eqr (by simpa using (hnum i).2 j)
    have hEi : toRealVec E₁.inf = toRealVec E₂.inf := funext fun i => eqr (hnum i).1.1.2
    have hEs : toRealVec E₁.sup = toRealVec E₂.sup := funext fun i => eqr (hnum i).1.2
    have hPn : P₁.nominal = P₂.nominal := HPolytope.isequal_nominal hP
    -- the error boxes read as the same real box
    have hE : E₁.construct = E₂.construct := by
      have : E₁.nominal = E₂.nominal := by
        have e₁ : RealImage.realImage E₁.inf = RealImage.realImage E₂.inf := hEi
        have e₂ : RealImage.realImage E₁.sup = RealImage.realImage E₂.sup := hEs
        simp only [Interval.nominal, e₁, e₂]
      unfold Interval.construct
      rw [this]
    have hN : (nominal (⟨h₁, c₁, G₁, P₁, E₁⟩ : ConZonotope 𝕋 (Vec 𝕋 n))) =
        nominal (⟨h₁, c₂, G₂, P₂, E₂⟩ : ConZonotope 𝕋 (Vec 𝕋 n)) := by
      show (⟨h₁, toRealVec c₁, fun j => toRealVec (G₁ j), P₁.nominal⟩ :
          CORALean.Real.ConZonotope (Vec ℝ n)) =
        ⟨h₁, toRealVec c₂, fun j => toRealVec (G₂ j), P₂.nominal⟩
      rw [hc, hG, hPn]
    change ContSet.construct (nominal (⟨h₁, c₁, G₁, P₁, E₁⟩ : ConZonotope 𝕋 (Vec 𝕋 n))) +
      E₁.construct =
      ContSet.construct (nominal (⟨h₁, c₂, G₂, P₂, E₂⟩ : ConZonotope 𝕋 (Vec 𝕋 n))) + E₂.construct
    rw [hN, hE]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
