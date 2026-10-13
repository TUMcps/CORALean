module

public import CORALean.ContSet.Interval.Float.Operations.Lt

@[expose] public section

/-!
# `Interval.lt` is sound

A `true` answer is a strict inequality for every bound, `toReal_lt_of_ltStrict`, hence
containment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.lt_subset {I J : Interval (Vec 𝕋 n)} (h : Interval.lt I J = true) :
    I.construct ⊆ J.construct := by -- --- PROOF ---
  simp only [Interval.lt, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    forall_const] at h
  intro x hx j
  exact ⟨le_trans (toReal_lt_of_ltStrict (h j).1).le (hx j).1,
    le_trans (hx j).2 (toReal_lt_of_ltStrict (h j).2).le⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
