module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ContSet/Taylm/Real/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- =======================================  `Taylm.box`  ======================================== --
-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- CORA's normalized domain. -/
def Taylm.box (n : ℕ) : Set (Vec ℝ n) := {t | ∀ k, |t k| ≤ 1}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
