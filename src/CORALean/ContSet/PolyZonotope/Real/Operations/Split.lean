module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitParallelotope
public import CORALean.ContSet.Zonotope.Real.Operations.Split

@[expose] public section

/-!
# `PolyZonotope.split`

CORA's `split(pZ, gen)`: over-approximate the polynomial zonotope by the parallelotope
`P = reduce(zonotope(pZ), 'methC', 1)` (`splitParallelotope`) and halve `P` along the generator
`gen` (`Zonotope.split`: the generator halved in both halves, the center moved by `∓g/2`); the
halves are polynomial zonotopes `polyZonotope(c ∓ g/2, G', [])` with identity exponents and no
independent generators (`Zonotope.polyZonotope`). `Theorems.SplitOuter` says the halves cover `pZ`.

## Inputs
* `pZ` – polynomial zonotope
* `j` – generator index

## Output
* pair of polynomial zonotopes covering the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `split(pZ, gen)`: the two halves of the parallelotope along its generator `j`. -/
noncomputable def PolyZonotope.split (pZ : PolyZonotope (Vec ℝ n))
    (j : Fin pZ.splitParallelotope.h) : PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  ((pZ.splitParallelotope.split j).fst.polyZonotope,
    (pZ.splitParallelotope.split j).snd.polyZonotope)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
