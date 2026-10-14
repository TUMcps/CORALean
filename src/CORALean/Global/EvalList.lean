module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A polynomial given by its integer coefficients, evaluated

`evalL [a₀, a₁, …] x = a₀ + a₁ x + …` by Horner's rule. The derivative polynomials of `tan` and
`tanh` have integer coefficients, so a list of them is a computable stand-in for the real
polynomial that a Lagrange remainder bound is written with.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def evalL : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, x => a + x * evalL l x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
