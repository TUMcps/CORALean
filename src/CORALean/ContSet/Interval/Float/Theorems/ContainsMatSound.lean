module

public import CORALean.ContSet.Interval.Float.Operations.ContainsMat
public import CORALean.ContSet.Interval.Real.Definitions.ContainsMat

@[expose] public section

/-!
# `Interval.containsMat` is sound when it says `true`

A `true` answer is a certificate of the exact layer's `ContainsMat` of the nominal interval matrix
and the stored matrix at the stored tolerance: each comparison was made in the direction that
implies the exact one. A `false` answer claims nothing.

## Inputs
* `I` – interval matrix
* `M` – matrix
* `tol` – tolerance

## Hypotheses
* `h` – the float decision is `true`

## Conclusion
* the stored matrix is in the nominal box up to the stored tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.containsMat_sound (I : Interval (Mat 𝕋 m n)) (M : Mat 𝕋 m n) (tol : 𝕋)
    (h : I.containsMat M tol = true) : -- --- CONCL ---
    I.nominal.ContainsMat (toRealMat M) (toReal tol) := by -- --- PROOF ---
  -- a `true` within-test is the exact one: both differences round up, the bound rounds down
  have hw : ∀ a b : 𝕋, (le (maximum (subUp a b) (subUp b a)) tol = true ∨
      le (maximum (subUp a b) (subUp b a)) (mulDown tol (minimum (absolute a) (absolute b)))
        = true) → |toReal a - toReal b| ≤ toReal tol ∨
          |toReal a - toReal b| ≤ toReal tol * min |toReal a| |toReal b| := by
    intro a b hab
    have hd : |toReal a - toReal b| ≤ toReal (maximum (subUp a b) (subUp b a)) := by
      rw [toReal_maximum]
      have h1 := sub_le_subUp a b
      have h2 := sub_le_subUp b a
      exact abs_le.mpr ⟨by linarith [le_max_right (toReal (subUp a b)) (toReal (subUp b a))],
        by linarith [le_max_left (toReal (subUp a b)) (toReal (subUp b a))]⟩
    rcases hab with h1 | h1
    · exact Or.inl (le_trans hd (toReal_le_of_le h1))
    · refine Or.inr (le_trans hd (le_trans (toReal_le_of_le h1) (le_trans (mulDown_le_mul _ _) ?_)))
      rw [toReal_minimum, toReal_absolute, toReal_absolute]
  -- unfold the decision into one fact per column and entry
  simp only [Interval.containsMat, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    Bool.or_eq_true, forall_const] at h
  -- each entry test is the exact one or implies it
  intro j
  refine ⟨fun i => toReal_le_of_le ((h j).1 i), fun i => ⟨?_, ?_⟩⟩
  · rcases ((h j).2 i).1 with hl | hl
    · refine Or.inl (lt_of_lt_of_le (toReal_lt_of_ltStrict hl) ?_)
      have := addDown_le_add (M i j) tol
      exact this
    · exact Or.inr (hw _ _ hl)
  · rcases ((h j).2 i).2 with hu | hu
    · refine Or.inl (lt_of_le_of_lt ?_ (toReal_lt_of_ltStrict hu))
      have := sub_le_subUp (M i j) tol
      exact this
    · exact Or.inr (hw _ _ hu)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
