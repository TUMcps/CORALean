module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Derivatives of `arccos` are those of `arcsin`, negated

`arccos' = -arcsin'` on all of `ℝ` (both are `∓1 / √(1 - x²)`, with the junk value `0` outside
`(-1, 1)`), so from the first derivative on `arccos⁽ᵏ⁾ = -arcsin⁽ᵏ⁾`.

## Inputs
* `j` – derivative order minus one

## Hypotheses
* none

## Conclusion
* the derivative of arccos is the negated derivative of arcsin
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
