module

public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleSpectraShadowExact

@[expose] public section

/-!
# A capsule lies in its spectrahedral shadow

Exact for `0 ≤ r` (`Capsule.spectraShadow_exact`); a negative radius is the empty capsule.

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* capsule is contained in its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.spectraShadow_contains (C : Capsule n) :
    C.construct ⊆ C.spectraShadow.construct := by
  rcases lt_or_ge C.r 0 with hr | hr
  · rw [Capsule.construct_eq_empty hr]
    exact Set.empty_subset _
  · exact (C.spectraShadow_exact hr).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
