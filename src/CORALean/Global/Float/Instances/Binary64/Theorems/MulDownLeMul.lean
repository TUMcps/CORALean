module

public import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
public import CORALean.Global.Float.Instances.Binary64.Operations.Basic

@[expose] public section

/-!
# Multiplication, rounded down, never overshoots

`mulDown` negates one argument rather than two: a product changes sign with
either factor, where a sum needs both. Otherwise the reading is `AddDownLeAdd`'s
— the upward assumption at `-a`, turned around by `toReal_neg`.

## Inputs
* `a` – first factor
* `b` – second factor

## Hypotheses
* none

## Conclusion
* the downward product is at most the real product
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Binary64


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulDown_le_mul (a b : Float) :
    toReal (mulDown a b) ≤ toReal a * toReal b := by -- --- PROOF ---
  rw [mulDown, trustedHardware.toReal_neg]
  -- one negated factor, so the assumed bound arrives already carrying `-`
  have h := trustedHardware.mul_le_mulUp (-a) b
  rw [trustedHardware.toReal_neg, neg_mul] at h
  linarith

end CORALean.Float.Binary64


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
