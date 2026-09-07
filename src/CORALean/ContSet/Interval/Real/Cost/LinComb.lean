import CORALean.ContSet.Interval.Real.Operations.LinComb
import CORALean.Global.Cost

/-!
# `Interval.linCombCost`

Asserted, not proved: `Operations/LinComb.lean` is the entrywise hull, one
`min` per entry of `inf` and one `max` per entry of `sup`, so at `Vec ℝ n` it
costs the same `2 * n` as `plus` — no interpolating generator to build, a box
having no generators to pair.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.linComb` costs at `Vec ℝ n`: one `min` per entry of `inf`
and one `max` per entry of `sup`. -/
def Interval.linCombCost (n : ℕ) : Cost := ⟨2 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
