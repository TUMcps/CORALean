module

public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

@[expose] public section

/-!
# The static abstraction error, kept as a polynomial

CORA's `priv_precompStatError` at `tensorOrder = 2`: `0.5*quadMap(Z,H)`, the second-order term of
the expansion evaluated on the set itself rather than boxed. `quadMapDep` keeps it in the factors
`pZ` is written in, where `quadMap` would run `dependent` first. Two departures from CORA, both in
what the caller does: the shift by the linearization point is here, `linReach` having done it
before the call; and `Q` is the halved Hessian family. A caller wanting all of `construct pZ`
covered runs `dependent` on `pZ` first, which is exact.

## Inputs
* `Q` – halved Hessian family
* `xs` – linearization point
* `pZ` – polynomial zonotope

## Output
* the second-order term as a polynomial zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The second-order term of the expansion at `xs`, as a polynomial zonotope
over `pZ`'s own factors. -/
def precompStatError (Q : Fin n → Mat ℝ n n) (xs : Vec ℝ n) (pZ : Real.PolyZonotope (Vec ℝ n)) :
    Real.PolyZonotope (Vec ℝ n) :=
  Real.PolyZonotope.quadMapDep Q { pZ with c := pZ.c - xs }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
