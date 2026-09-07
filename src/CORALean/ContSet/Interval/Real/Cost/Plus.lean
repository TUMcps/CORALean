import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.Global.Cost

/-!
# `Interval.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two lower bounds and the
two upper bounds entrywise, so at `Vec ℝ n` it is `2 * n` additions and nothing
else. No rounding enters here — that is the float layer's cost, not this one's.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.plus` costs at `Vec ℝ n`: one addition per entry of `inf`
and one per entry of `sup`. -/
def Interval.plusCost (n : ℕ) : Cost := ⟨2 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
