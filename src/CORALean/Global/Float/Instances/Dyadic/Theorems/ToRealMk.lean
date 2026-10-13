module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# A dyadic literal, read back

`toReal_def` restated at an anonymous constructor, which is the form
`quotDown_le_div` and `le_quotUp` both rewrite with after computing a quotient.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_mk (m e : ℤ) : toReal (⟨m, e⟩ : Dyadic p) = (m : ℝ) * 2 ^ e :=
  toReal_def _

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
