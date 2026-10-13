module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger

@[expose] public section

/-!
# `Ellipsoid.isBiggerCora`

CORA's `@ellipsoid/isBigger` as the code answers: in dimension `1` it returns `true` before
looking at the ellipsoids (`if dim(E1)==1 res = true`), otherwise the test of `isBigger`.
`isBigger_cora_counterexample` shows the shortcut is wrong.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isBiggerCora (E₁ E₂ : Ellipsoid n) : Prop := n = 1 ∨ E₁.isBigger E₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
