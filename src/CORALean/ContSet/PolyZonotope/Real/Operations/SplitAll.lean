import CORALean.ContSet.PolyZonotope.Real.Operations.Split

/-!
# `PolyZonotope.splitAll`

CORA's `split(pZ)` without `gen`: the pair of halves along every generator of the parallelotope.
CORA loops over the `n` generators of `P` and errors when `methC` leaves fewer; here the loop
runs over the generators there are.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.splitAll (pZ : PolyZonotope (Vec ℝ n)) :
    Fin pZ.splitParallelotope.h → PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  fun j => pZ.split j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
