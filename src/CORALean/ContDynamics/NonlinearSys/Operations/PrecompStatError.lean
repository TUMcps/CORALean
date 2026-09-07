import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

/-!
# The static abstraction error, kept as a polynomial

CORA's `priv_precompStatError` at `tensorOrder = 2`: `0.5*quadMap(Z,H)`, the
second-order term of the expansion evaluated on the set itself rather than
boxed. `quadMapDep` is what keeps it in the factors `pZ` is written in — `quadMap`
would run `dependent` first and index the result by `p + q` fresh factors
instead.

Two departures from CORA's file, both in what the caller does rather than in what
is computed. The shift by the linearization point is here, `linReach` having done
it before the call; and `Q` is the *halved* Hessian family, so no scalar multiple
is needed on the way out. CORA's `Z` is the set extended by a zero input block,
which contributes nothing, so `Q` is square in the state alone.

A caller wanting the whole of `construct pZ` covered runs `dependent` on `pZ`
first, which is exact and empties the independent block.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The second-order term of the expansion at `xs`, as a polynomial zonotope
over `pZ`'s own factors. -/
def precompStatError (Q : Fin n → Mat ℝ n n) (xs : Vec ℝ n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) :=
  PolyZonotope.quadMapDep Q { pZ with c := pZ.c - xs }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
