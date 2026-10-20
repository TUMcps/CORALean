module

public import CORALean.ContSet.Zonotope.Float.Operations.ErrBound
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `errBound` bounds every member of a float box

A value between `inf` and `sup` is at most the larger absolute end in magnitude.

## Inputs
* `E` – error box
* `e` – point
* `i` – entry

## Hypotheses
* `he` – point lies in the box

## Conclusion
* entry magnitude is bounded by the larger absolute end
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.abs_le_errBound (E : Interval (Vec 𝕋 n)) {e : Vec ℝ n} (he : e ∈ E.construct)
    (i : Fin n) : |e i| ≤ toReal (Zonotope.errBound E i) := by -- --- PROOF ---
  have h1 : toReal (E.inf i) ≤ e i := (he i).1
  have h2 : e i ≤ toReal (E.sup i) := (he i).2
  simp only [Zonotope.errBound, toReal_maximum, toReal_absolute]
  have a1 := neg_abs_le (toReal (E.inf i))
  have a2 := le_abs_self (toReal (E.sup i))
  have m1 := le_max_left |toReal (E.inf i)| |toReal (E.sup i)|
  have m2 := le_max_right |toReal (E.inf i)| |toReal (E.sup i)|
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
