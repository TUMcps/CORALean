module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
public import CORALean.Global.Float.Instances.IEEE.Operations.MulUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp

@[expose] public section

/-!
# Multiplication, rounded up, never undershoots

The exact product is `Dyadic`'s, and `le_roundUp` rounds it up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mul_le_mulUp (a b : IEEE fmt) : a.toReal * b.toReal ≤ (mulUp a b).toReal :=
  calc a.toReal * b.toReal = (Dyadic.exactMul a.toDyadic b.toDyadic).toReal :=
        (Dyadic.toReal_exactMul _ _).symm
    _ ≤ _ := le_roundUp _

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
