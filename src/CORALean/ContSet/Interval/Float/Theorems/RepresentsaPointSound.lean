module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.representsa_point` is sound

A `true` answer squeezes every coordinate to `toReal (inf j)`, so the box is that single point.

## Inputs
* `I` – interval box

## Hypotheses
* `h` – test returned true

## Conclusion
* the box represents a single point
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

theorem Interval.representsa_point_sound {I : Interval (Vec 𝕋 n)}
    (h : I.representsa_point = true) : ∃ v, I.construct = {v} := by -- --- PROOF ---
  simp only [Interval.representsa_point, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    forall_const] at h
  refine ⟨fun j => toReal (I.inf j), ?_⟩
  ext x
  constructor
  · intro hx
    refine funext fun j => le_antisymm ?_ (hx j).1
    exact le_trans (hx j).2 (toReal_le_of_le (h j).1)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fun j => ⟨le_refl _, toReal_le_of_le (h j).2⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
