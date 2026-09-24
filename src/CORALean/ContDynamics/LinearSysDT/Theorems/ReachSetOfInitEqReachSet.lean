import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetOfInit

/-!
# `reachSetOfInit` at `construct R₀` is `reachSet`

Both are the same recursion, one starting from a bare set and the other from a
representation's `construct`; reading the bare set back as `construct R₀`
makes every step line up, by induction.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.WithInput.reachSetOfInit_eq_reachSet (sys : LinearSysDT.WithInput 𝕋 S n)
    (R₀ : S n) (k : ℕ) :
    sys.reachSetOfInit (construct R₀) k = sys.sys.reachSet R₀ sys.U k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [LinearSysDT.WithInput.reachSetOfInit, LinearSysDT.reachSet, ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
