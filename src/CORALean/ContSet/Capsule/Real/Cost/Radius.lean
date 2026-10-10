import CORALean.ContSet.Capsule.Real.Operations.Radius
import CORALean.Global.Cost

/-!
# `Capsule.radiusCost`

Asserted, not proved: `Operations/Radius.lean` is `‖g‖₂ + r`: the squared length
(`2 * n`), its `sqrt` and one addition.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.radius` costs at `Vec ℝ n`. -/
def Capsule.radiusCost (n : ℕ) : Cost := ⟨2 * n + 2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
