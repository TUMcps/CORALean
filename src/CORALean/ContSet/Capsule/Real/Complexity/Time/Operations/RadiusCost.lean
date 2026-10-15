module

public import CORALean.ContSet.Capsule.Real.Operations.Radius
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.radiusCost`

Asserted, not proved: `Operations/Radius.lean` is `‖g‖₂ + r`: the squared length
(`2 * n`), its `sqrt` and one addition.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.radius` costs at `Vec ℝ n`: the squared length, its root, the sum, and one write
of the scalar. -/
def Capsule.radiusCost (n : ℕ) : Cost := ⟨2 * n + 3⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
