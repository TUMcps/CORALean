import CORALean.Global.Float.FloatOps

/-!
# A sum leaving one index out, rounded up

`Fin n` has no index type for "everything but `i`", so the `i`-th term is zeroed instead and
the sum taken over all of `Fin n`, `sumUp` rounding each partial sum up.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑_{j ≠ i} v j`, the `i`-th term zeroed, rounded up. -/
def sumOffUp (i : Fin n) (v : Fin n → 𝕋) : 𝕋 :=
  sumUp fun j => if j = i then zero else v j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
