module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs

@[expose] public section

/-!
# `NonlinearReset.secondOrderBound`: the second-order term of output `i`

`aux_tensorOrder2` of `hybridDynamics/@nonlinearReset/evaluate.m` (l. 109-137) bounds the
Lagrange remainder of output `i` by `0.5 * dz' * H_ * dz`, where `dz` is the largest deviation of
the state and input from the expansion point in each coordinate and `H_ = max(infimum(abs(H)),
supremum(abs(H)))` the entrywise bound of the interval Hessian of that output. `Habs i a b` is the
entry `(a, b)` of `H_` for output `i`; the remainder is the interval `[-s, s]`.

## Inputs
* `α` – scalar field
* `q` – number of outputs
* `d` – state dimension
* `Habs` – absolute Hessian bounds
* `dz` – state radius
* `i` – output index

## Output
* second-order term of output `i`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The second-order bound of output `i` over `d` coordinates with the Hessian bound of that
output. -/
def NonlinearReset.secondOrderBound {α : Type} [Field α] {q d : Nat}
    (Habs : Fin q → Fin d → Fin d → α) (dz : Fin d → α) (i : Fin q) : α :=
  (1 / 2) * ∑ a, ∑ b, dz a * Habs i a b * dz b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
