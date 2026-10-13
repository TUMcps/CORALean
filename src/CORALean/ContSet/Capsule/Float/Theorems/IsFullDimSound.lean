import CORALean.ContSet.Capsule.Float.Operations.IsFullDim
import CORALean.ContSet.Capsule.Real.Theorems.IsFullDimIff

/-!
# `Capsule.isFullDim` is sound

`true` is one of the exact layer's cases (`Capsule.isFullDim_iff`) at the nominal capsule, each
read off the certificate: `ltStrict` is a strict inequality, `le` a weak one, and a certified
positive `|g j|` makes `g` nonzero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isFullDim_sound {C : Capsule 𝕋 n} (h : Capsule.isFullDim C = true) :
    (interior C.construct).Nonempty := by -- --- PROOF ---
  refine (CORALean.Real.Capsule.isFullDim_iff C.nominal).mpr ?_
  simp only [Capsule.isFullDim, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_finRange, true_and] at h
  rcases h with h | ⟨h0, h | ⟨h1, j, hj⟩⟩
  · -- a certified positive radius
    left
    have := toReal_lt_of_ltStrict h
    rw [toReal_zero] at this
    exact this
  · -- a nonnegative radius in dimension `0`
    right
    have hr0 : 0 ≤ C.nominal.r := by
      have := toReal_le_of_le h0; rw [toReal_zero] at this; exact this
    exact ⟨hr0, Or.inl h⟩
  · -- a nonnegative radius on the line, with a coordinate of `g` certified nonzero
    right
    have hr0 : 0 ≤ C.nominal.r := by
      have := toReal_le_of_le h0; rw [toReal_zero] at this; exact this
    refine ⟨hr0, Or.inr ⟨h1, ?_⟩⟩
    intro hz
    have := toReal_lt_of_ltStrict hj
    rw [toReal_zero, toReal_absolute] at this
    have hg : toReal (C.g j) = 0 := congrFun hz j
    rw [hg, abs_zero] at this
    exact lt_irrefl _ this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
