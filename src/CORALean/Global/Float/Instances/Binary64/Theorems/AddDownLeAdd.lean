module

public import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
public import CORALean.Global.Float.Instances.Binary64.Operations.AddDown

@[expose] public section

/-!
# Addition, rounded down, never overshoots

`addDown` is `addUp` between two negations, so this is the upward assumption
read through `toReal_neg` and nothing else: the machine is assumed to round one
step up, and a step up on the negated arguments is a step down here. No second
assumption about the hardware is needed, which is the point of defining the
downward operations as mirrors rather than as primitives.
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Binary64


-- =======================================  MAIN THEOREM  ======================================= --

theorem addDown_le_add (a b : Float) :
    toReal (addDown a b) ≤ toReal a + toReal b := by -- --- PROOF ---
  rw [addDown, trustedHardware.toReal_neg]
  -- the same assumption at `-a` and `-b`, where the step up is a step down here
  have h := trustedHardware.add_le_addUp (-a) (-b)
  rw [trustedHardware.toReal_neg, trustedHardware.toReal_neg] at h
  linarith

end CORALean.Float.Binary64


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
