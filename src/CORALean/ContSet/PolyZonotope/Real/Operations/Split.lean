import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitParallelotope
import CORALean.ContSet.Zonotope.Real.Operations.Split

/-!
# `PolyZonotope.split`

CORA's `split(pZ, gen)`: over-approximate the polynomial zonotope by the parallelotope
`P = reduce(zonotope(pZ), 'methC', 1)` (`splitParallelotope`) and halve `P` along the generator
`gen` (`Zonotope.split`: the generator halved in both halves, the centre moved by `∓g/2`); the
halves are polynomial zonotopes `polyZonotope(c ∓ g/2, G', [])` with identity exponents and no
independent generators (`Zonotope.polyZonotope`). `Theorems.SplitOuter` says the halves cover `pZ`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `split(pZ, gen)`: the two halves of the parallelotope along its generator `j`. -/
noncomputable def PolyZonotope.split (pZ : PolyZonotope (Vec ℝ n))
    (j : Fin pZ.splitParallelotope.h) : PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  ((pZ.splitParallelotope.split j).1.polyZonotope,
    (pZ.splitParallelotope.split j).2.polyZonotope)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
