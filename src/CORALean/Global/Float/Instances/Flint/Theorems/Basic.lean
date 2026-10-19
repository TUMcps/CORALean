module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.Instances.Flint.Operations.Basic

@[expose] public section

/-!
# `Global/Float/Instances/Flint/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float.Flint

variable {p : ℕ}


-- ======================================  `toReal_half`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Dyadic.toReal_half` at the same pair: `half` builds the pair `Dyadic.half`
does. -/
theorem toReal_half (a : Flint p) : toReal (half a) = toReal a / 2 :=
  Dyadic.toReal_half a.toDyadic


-- ====================================  `toReal_le_of_le`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le` is `Dyadic.le` of the same pairs, so this is `Dyadic.toReal_le_of_le`. -/
theorem toReal_le_of_le {a b : Flint p} (h : le a b = true) : toReal a ≤ toReal b :=
  Dyadic.toReal_le_of_le h


-- =======================================  `toReal_neg`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- `Dyadic.toReal_neg` at the same pair: `neg` builds the pair `Dyadic.neg` does. -/
theorem toReal_neg (a : Flint p) : toReal (neg a) = -toReal a :=
  Dyadic.toReal_neg a.toDyadic

end CORALean.Float.Flint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
