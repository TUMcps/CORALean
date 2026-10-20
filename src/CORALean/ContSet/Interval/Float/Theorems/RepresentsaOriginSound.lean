module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.representsa_origin` is sound

A `true` answer squeezes both bounds of every coordinate to `0`, so the box is `{0}`.

## Inputs
* `I` – interval box

## Hypotheses
* `h` – test returned true

## Conclusion
* the box represents exactly the origin
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

theorem Interval.representsa_origin_sound {I : Interval (Vec 𝕋 n)}
    (h : I.representsa_origin = true) : I.construct = {0} := by -- --- PROOF ---
  simp only [Interval.representsa_origin, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    forall_const] at h
  have h1 : ∀ j, toReal (I.inf j) ≤ 0 := fun j => by
    simpa [toReal_zero] using toReal_le_of_le (h j).1.1.1
  have h2 : ∀ j, 0 ≤ toReal (I.inf j) := fun j => by
    simpa [toReal_zero] using toReal_le_of_le (h j).1.1.2
  have h3 : ∀ j, toReal (I.sup j) ≤ 0 := fun j => by
    simpa [toReal_zero] using toReal_le_of_le (h j).1.2
  have h4 : ∀ j, 0 ≤ toReal (I.sup j) := fun j => by
    simpa [toReal_zero] using toReal_le_of_le (h j).2
  -- squeezed to `0` on both sides, so only the origin remains
  ext x
  constructor
  · intro hx
    refine funext fun j => le_antisymm ?_ ?_
    · exact le_trans (hx j).2 (h3 j)
    · exact le_trans (h2 j) (hx j).1
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fun j => ⟨h1 j, h4 j⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
