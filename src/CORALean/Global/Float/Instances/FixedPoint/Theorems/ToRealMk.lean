import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# A fixed-point literal, read back

`toReal_def` restated at an anonymous constructor, which is the form every
operation's own guarantee rewrites with after computing a mantissa and digit
count.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_mk (m : ℤ) (d : ℕ) : toReal (⟨m, d⟩ : FixedPoint f) = (m : ℝ) / 10 ^ d :=
  toReal_def _

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
