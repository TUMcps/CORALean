module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.MantissaPos
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDivEq
public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic

@[expose] public section

/-!
# Division, rounded up, never undershoots

The same fact as `LeRoundUp`, `Int.ediv_mul_le`, applied one step earlier: the
quotient is rounded while it is still two integers, since afterwards it is a
rational nothing on the grid equals. The upward direction is the downward
one, `quotDown_le_div`, at a negated dividend; the grid rounding on top,
`le_roundUp`, only moves the bound further out.

## Inputs
* `a` – dividend
* `b` – divisor

## Hypotheses
* `hb` – the divisor is positive

## Conclusion
* the real quotient is at most the upward quotient
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}

/-- The upward direction is the downward one at a negated dividend. -/
private theorem le_quotUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (quotUp a b) := by -- --- PROOF ---
  have hm : 0 < b.mantissa := mantissa_pos hb
  have hmR : (0 : ℝ) < (b.mantissa : ℝ) := Int.cast_pos.mpr hm
  rw [toReal_div_eq a b (p + b.mantissa.natAbs.log2 + 1) (ne_of_gt hmR), quotUp, toReal_mk]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  rw [div_le_iff₀ hmR]
  set s := p + b.mantissa.natAbs.log2 + 1
  have h := Int.ediv_mul_le (-(a.mantissa * 2 ^ s)) (ne_of_gt hm)
  have h' : a.mantissa * 2 ^ s
      ≤ -(-(a.mantissa * 2 ^ s) / b.mantissa) * b.mantissa := by
    rw [neg_mul]
    linarith
  exact_mod_cast h'


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_divUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (divUp a b) :=
  le_trans (le_quotUp a b hb) (le_roundUp _)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
