module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealNeg
public import CORALean.Global.Float.Instances.Flint.Operations.Neg

@[expose] public section

/-!
# Negation is exact

`Dyadic.toReal_neg` at the same pair: `neg` builds the pair `Dyadic.neg` does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Flint

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_neg (a : Flint p) : toReal (neg a) = -toReal a :=
  Dyadic.toReal_neg a.toDyadic

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
