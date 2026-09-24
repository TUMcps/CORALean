import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
import CORALean.Global.Float.Instances.Binary64.Operations.MulDown

/-!
# Multiplication, rounded down, never overshoots

`mulDown` negates one argument rather than two: a product changes sign with
either factor, where a sum needs both. Otherwise the reading is `AddDownLeAdd`'s
— the upward assumption at `-a`, turned around by `toReal_neg`.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


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
