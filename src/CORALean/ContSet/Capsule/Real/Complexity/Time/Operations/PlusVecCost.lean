module

public import CORALean.ContSet.Capsule.Real.Operations.PlusVec
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.plusVecCost`

Asserted, not proved: `Operations/PlusVec.lean` shifts the center, `n` additions;
the generator and radius are copied.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.plusVec` costs at `Vec ℝ n`. -/
def Capsule.plusVecCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
