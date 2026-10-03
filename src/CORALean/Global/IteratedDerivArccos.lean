import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivatives of `arccos` are those of `arcsin`, negated

`arccos' = -arcsin'` on all of `ℝ` (both are `∓1 / √(1 - x²)`, with the junk value `0` outside
`(-1, 1)`), so from the first derivative on `arccos⁽ᵏ⁾ = -arcsin⁽ᵏ⁾`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem iteratedDeriv_arccos_succ (j : ℕ) :
    iteratedDeriv (j + 1) Real.arccos = -iteratedDeriv (j + 1) Real.arcsin := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', Real.deriv_arccos, Real.deriv_arcsin]
  funext x
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
