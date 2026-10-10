import CORALean.ContSet.Capsule.Real.Operations.PlusVec
import CORALean.Global.Cost

/-!
# `Capsule.plusVecCost`

Asserted, not proved: `Operations/PlusVec.lean` shifts the centre, `n` additions;
the generator and radius are copied.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.plusVec` costs at `Vec ℝ n`. -/
def Capsule.plusVecCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
