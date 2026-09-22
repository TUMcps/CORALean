import CORALean.Global.Float.Instances.Binary64.Axioms

/-!
# Division, rounded down, never overshoots

The dividend is what gets negated, so the divisor stays positive and the assumed
bound applies unchanged — which is why `divDown` mirrors `a` and not `b`, and
why this needs the same hypothesis on the divisor that `div_le_divUp` carries
and no more.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


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
