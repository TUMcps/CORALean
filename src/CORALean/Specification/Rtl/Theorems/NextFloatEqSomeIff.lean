module

public import CORALean.Specification.Rtl.Definitions.IsHalfMultiple
public import CORALean.Specification.Rtl.Operations.NextFloat

@[expose] public section

/-!
# What `nextFloat?` succeeds with

Over a float scalar `nextFloat?` succeeds exactly for the times that denote a multiple of `0.5` up
to `1e-8` (`IsHalfMultiple` of the real they denote), with the shifted object.

## Inputs
* `a` – operand
* `ψ` – object
* `t` – time shift

## Hypotheses
* none

## Conclusion
* the result is `ψ` iff `ψ` is the shifted object and the time denotes a multiple of `0.5`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 L : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Rtl.nextFloat?_eq_some_iff (a ψ : Rtl 𝕋 L) (t : 𝕋) : -- --- CONCL ---
    Rtl.nextFloat? a t = some ψ ↔
      ψ = .next t a ∧ Rtl.IsHalfMultiple (SoundFloatArithmetic.toReal t) := by -- --- PROOF ---
  -- the test on the exact decoding is the test on the real it denotes
  have h : (ToRat.toRat t - ⌊ToRat.toRat t / (1 / 2)⌋ * (1 / 2) ≤ 1 / 10 ^ 8) ↔
      Rtl.IsHalfMultiple (SoundFloatArithmetic.toReal t) := by
    unfold Rtl.IsHalfMultiple
    rw [← ToRat.toReal_toRat t, ← Rat.cast_le (K := ℝ)]
    have := Rat.floor_cast (α := ℝ) (ToRat.toRat t / (1 / 2))
    push_cast at this ⊢
    rw [this]
  unfold Rtl.nextFloat?
  by_cases hc : ToRat.toRat t - ⌊ToRat.toRat t / (1 / 2)⌋ * (1 / 2) ≤ 1 / 10 ^ 8
  · rw [if_pos hc]
    simp [h.mp hc, eq_comm]
  · rw [if_neg hc]
    simp [mt h.mpr hc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
