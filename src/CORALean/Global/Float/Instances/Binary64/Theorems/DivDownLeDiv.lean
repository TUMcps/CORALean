module

public import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
public import CORALean.Global.Float.Instances.Binary64.Operations.DivDown

@[expose] public section

/-!
# Division, rounded down, never overshoots

The dividend is what gets negated, so the divisor stays positive and the assumed
bound applies unchanged — which is why `divDown` mirrors `a` and not `b`, and
why this needs the same hypothesis on the divisor that `div_le_divUp` carries
and no more.

## Inputs
* `a` – dividend
* `b` – divisor

## Hypotheses
* `hb` – the divisor is positive

## Conclusion
* the downward quotient is at most the real quotient
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Binary64


-- =======================================  MAIN THEOREM  ======================================= --

theorem divDown_le_div (a b : Float) (hb : 0 < toReal b) :
    toReal (divDown a b) ≤ toReal a / toReal b := by -- --- PROOF ---
  rw [divDown, trustedHardware.toReal_neg]
  -- the divisor is untouched, so the positivity hypothesis passes straight on
  have h := trustedHardware.div_le_divUp (-a) b hb
  rw [trustedHardware.toReal_neg, neg_div] at h
  linarith

end CORALean.Float.Binary64


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
