module

public import CORALean.NN.Layers.Definitions.EvalPoly
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A degree-1 polynomial is an affine map

ℝ-only, as `evalPoly` is: the order-1 case, as a relaxation writes its affine map.

## Inputs
* `c` – coefficients of a degree-one polynomial
* `t` – evaluation point

## Hypotheses
* none

## Conclusion
* the polynomial is the affine map with those coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_one (c : Fin 2 → ℝ) (t : ℝ) : evalPoly c t = c 1 * t + c 0 := by
  show ∑ i, c i * t ^ (i : ℕ) = _
  rw [Fin.sum_univ_two]
  show c 0 * t ^ (0 : ℕ) + c 1 * t ^ (1 : ℕ) = _
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
