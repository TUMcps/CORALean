module

public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The halves of a proper box are proper boxes inside it
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.halveBox_sub {B : Fin n → ℝ × ℝ} (hB : ∀ k, (B k).1 ≤ (B k).2) (β : Fin n) :
    (∀ k, ((Taylm.halveBox B β).1 k).1 ≤ ((Taylm.halveBox B β).1 k).2) ∧
      (∀ k, ((Taylm.halveBox B β).2 k).1 ≤ ((Taylm.halveBox B β).2 k).2) ∧
      (∀ t, Taylm.InBox (Taylm.halveBox B β).1 t → Taylm.InBox B t) ∧
      (∀ t, Taylm.InBox (Taylm.halveBox B β).2 t → Taylm.InBox B t) := by -- --- PROOF ---
  have hm := hB β
  refine ⟨fun k => ?_, fun k => ?_, fun t ht k => ?_, fun t ht k => ?_⟩
  -- coordinate `β` is halved, the others are kept
  · simp only [Taylm.halveBox, Function.update_apply]; split_ifs with hk
    · subst hk; simp only; linarith
    · exact hB k
  · simp only [Taylm.halveBox, Function.update_apply]; split_ifs with hk
    · subst hk; simp only; linarith
    · exact hB k
  · have := ht k
    simp only [Taylm.halveBox, Function.update_apply] at this; split_ifs at this with hk
    · subst hk; exact ⟨this.1, by linarith [this.2]⟩
    · exact this
  · have := ht k
    simp only [Taylm.halveBox, Function.update_apply] at this; split_ifs at this with hk
    · subst hk; exact ⟨by linarith [this.1], this.2⟩
    · exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
