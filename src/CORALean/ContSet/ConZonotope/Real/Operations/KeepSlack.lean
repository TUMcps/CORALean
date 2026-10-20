module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ConZonotope.keepSlack`

What a constraint can gain from the coefficients a partition drops: they range
over `[-1, 1]`, so a row `a · β` moves by at most `∑ |aₗ|` over the dropped
coordinates `l`. Zero exactly when the row does not see them, which is when
dropping them costs the row nothing.

## Inputs
* `part` – partition of the generators
* `f` – constraint functional

## Output
* the slack the dropped coefficients can contribute
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {h q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑ₗ |f e_{right l}|`: the most the dropped coefficients can move the row `f`. -/
noncomputable def ConZonotope.keepSlack (part : Split (Fin h) into (Fin q) ⊕ (Fin r))
    (f : Vec ℝ h →ₗ[ℝ] ℝ) : ℝ :=
  ∑ l, |f (Pi.single (part.right l) (1 : ℝ) : Vec ℝ h)|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
