module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Isequal
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.isequal` is sound

A `true` answer says the stored numbers agree as real numbers and the exponent matrices agree, so
the nominal sets are the same and the error boxes are the same, and the denoted sets are equal.
`false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isequal_sound {Z S : ConPolyZono 𝕋 (Vec 𝕋 n)} (h : Z.isequal S = true) :
    Z.construct = S.construct := by -- --- PROOF ---
  unfold ConPolyZono.isequal at h
  split at h
  · rename_i e
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
      beq_iff_eq] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨⟨hnum, hcon⟩, hE⟩ := h
    obtain ⟨p₁, h₁, qI₁, c₁, G₁, E₁, GI₁, ⟨m₁, q₁, A₁, R₁, b₁, s₁, o₁, d₁⟩, ho₁, hd₁, r₁⟩ := Z
    obtain ⟨p₂, h₂, qI₂, c₂, G₂, E₂, GI₂, ⟨m₂, q₂, A₂, R₂, b₂, s₂, o₂, d₂⟩, ho₂, hd₂, r₂⟩ := S
    simp only at e hnum hcon hE
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
    -- every row of both is an equation, so the operators agree too
    obtain rfl : o₁ = o₂ := funext fun i => (ho₁ i).trans (ho₂ i).symm
    -- and both boxes are the unit box
    obtain rfl : d₁ = d₂ := hd₁.trans hd₂.symm
    simp only [Fin.cast_eq_self] at hnum hcon hE
    have hc : toRealVec c₁ = toRealVec c₂ := funext fun i => eqr (hnum i).1.1.1.1
    have hG : (fun l i => toReal (G₁ l i)) = fun l i => toReal (G₂ l i) :=
      funext fun l => funext fun i => eqr (by simpa using (hnum i).1.2 l)
    have hGI : (fun l i => toReal (GI₁ l i)) = fun l i => toReal (GI₂ l i) :=
      funext fun l => funext fun i => eqr (by simpa using (hnum i).2 l)
    have hEi : toRealVec r₁.inf = toRealVec r₂.inf := funext fun i => eqr (hnum i).1.1.1.2
    have hEs : toRealVec r₁.sup = toRealVec r₂.sup := funext fun i => eqr (hnum i).1.1.2
    -- the constraints, then the exponent matrices
    have hA : toRealMat A₁ = toRealMat A₂ :=
      funext fun r => funext fun j => eqr (by simpa using (hcon r).2 j)
    have hb : toRealVec b₁ = toRealVec b₂ := funext fun r => eqr (hcon r).1.1
    have hs : toRealVec s₁ = toRealVec s₂ := funext fun r => eqr (hcon r).1.2
    have hE₁ : E₁ = E₂ := funext fun k => funext fun j => (by simpa using (hE k).1 j)
    have hE₂ : R₁ = R₂ := funext fun k => funext fun j => (by simpa using (hE k).2 j)
    -- the interval fields read as the same real boxes
    have hint : ∀ {m : ℕ} {u v : Interval (Vec 𝕋 m)}, toRealVec u.inf = toRealVec v.inf →
        toRealVec u.sup = toRealVec v.sup → u.nominal = v.nominal := by
      intro m u v e₁ e₂
      have e₁' : RealImage.realImage u.inf = RealImage.realImage v.inf := e₁
      have e₂' : RealImage.realImage u.sup = RealImage.realImage v.sup := e₂
      simp only [Interval.nominal, e₁', e₂']
    -- the error boxes
    have hr : r₁.construct = r₂.construct := by
      unfold Interval.construct
      rw [hint hEi hEs]
    -- so the nominal sets are the same
    have hdn : d₁.nominal = Real.Interval.unit p₁ :=
      (congrArg Interval.nominal hd₁).trans (Interval.nominal_unit _)
    -- the two sets, named once
    set Z' : ConPolyZono 𝕋 (Vec 𝕋 n) :=
      ⟨p₁, h₁, qI₁, c₁, G₁, E₁, GI₁, ⟨m₁, q₁, A₁, R₁, b₁, s₁, o₁, d₁⟩, ho₁, hd₁, r₁⟩ with hZ'
    set S' : ConPolyZono 𝕋 (Vec 𝕋 n) :=
      ⟨p₁, h₁, qI₁, c₂, G₂, E₂, GI₂, ⟨m₁, q₁, A₂, R₂, b₂, s₂, o₁, d₁⟩, ho₂, hd₂, r₂⟩ with hS'
    have hN : nominal Z' = nominal S' := by
      show CORALean.Real.ConPolyZono.relax (⟨p₁, h₁, qI₁, toRealVec c₁,
          fun l i => toReal (G₁ l i), E₁, fun j i => toReal (GI₁ j i),
          ⟨m₁, q₁, toRealMat A₁, R₁, toRealVec b₁, o₁, d₁.nominal⟩, ho₁, hdn⟩ :
            CORALean.Real.ConPolyZono (Vec ℝ n)) (toRealVec s₁) =
        CORALean.Real.ConPolyZono.relax ⟨p₁, h₁, qI₁, toRealVec c₂,
          fun l i => toReal (G₂ l i), E₂, fun j i => toReal (GI₂ j i),
          ⟨m₁, q₁, toRealMat A₂, R₂, toRealVec b₂, o₁, d₁.nominal⟩, ho₂, hdn⟩ (toRealVec s₂)
      rw [hc, hG, hGI, hE₁, hE₂, hA, hb, hs]
    -- the sum of nominal set and error box, on both sides
    change ContSet.construct (nominal Z') + r₁.construct
      = ContSet.construct (nominal S') + r₂.construct
    rw [hN, hr]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
