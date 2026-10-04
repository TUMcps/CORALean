import CORALean.ContSet.PolyZonotope.Real.Operations.SubsMul

/-!
# `PolyZonotope.subsPow`

CORA's `Y{i,j}`: the `d`-th power of a sum of monomials, by repeated `priv_multiply`, the empty
product being the term `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `d`-th power of a sum of monomials. -/
noncomputable def PolyZonotope.subsPow {p : ℕ} (A : List (ℝ × (Fin p → ℕ))) :
    ℕ → List (ℝ × (Fin p → ℕ))
  | 0 => [(1, 0)]
  | d + 1 => PolyZonotope.subsMul A (PolyZonotope.subsPow A d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
