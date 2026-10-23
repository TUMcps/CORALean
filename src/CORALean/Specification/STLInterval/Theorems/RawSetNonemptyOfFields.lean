module

public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# The fields of a nonempty interval give it a time

The proof fields of `STLInterval.nonempty`, an infinite upper end open and the lower bound below
the upper (or equal with both ends closed), make the times between the bounds nonempty: the
lower bound is finite, so `rawSet_nonempty_of` applies.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `b` – an infinite upper bound is open
* `c` – the lower bound is below the upper, or equal with both ends closed

## Conclusion
* the times between the bounds are nonempty
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.rawSet_nonempty_of_fields {l : 𝕋} {u : WithTop 𝕋} {lc rc : Bool}
    (b : u = ⊤ → rc = false) (c : ((toReal l : ℝ) : EReal) < STLInterval.toEReal u ∨
      (((toReal l : ℝ) : EReal) = STLInterval.toEReal u ∧ lc = true ∧ rc = true)) :
    (rawSet (toReal l : ℝ) (STLInterval.toEReal u) lc rc).Nonempty :=
  rawSet_nonempty_of _ _ _ _ (fun h => absurd h (EReal.coe_ne_bot _))
    (fun h => b ((STLInterval.toEReal_eq_top_iff u).1 h)) c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
