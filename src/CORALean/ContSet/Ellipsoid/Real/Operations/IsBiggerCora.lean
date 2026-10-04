import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger

/-!
# `Ellipsoid.isBiggerCora`

CORA's `@ellipsoid/isBigger` as the code answers: in dimension `1` it returns `true` before
looking at the ellipsoids (`if dim(E1)==1 res = true`), otherwise the test of `isBigger`.
`isBigger_cora_counterexample` shows the shortcut is wrong.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isBiggerCora (E₁ E₂ : Ellipsoid n) : Prop := n = 1 ∨ E₁.isBigger E₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
