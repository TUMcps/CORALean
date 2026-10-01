import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.Global.Partition

/-!
# `ConZonotope.keepSlack`

What a constraint can gain from the coefficients a partition drops: they range
over `[-1, 1]`, so a row `a · β` moves by at most `∑ |aₗ|` over the dropped
coordinates `l`. Zero exactly when the row does not see them, which is when
dropping them costs the row nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
