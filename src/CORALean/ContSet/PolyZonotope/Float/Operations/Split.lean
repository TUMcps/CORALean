module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitParallelotope
public import CORALean.ContSet.Zonotope.Float.Operations.Split

@[expose] public section

/-!
# `PolyZonotope.split`, over a floating-point scalar

CORA's `split(pZ, gen)`: the parallelotope `splitParallelotope` halved along its generator `gen`
(`Zonotope.split`: the generator halved in both halves, the centre moved by `∓g/2`, each centre
paying its rounding into the box), the halves read as polynomial zonotopes with identity exponents
and no independent generators (`Zonotope.polyZonotope`). `Theorems.SplitOuter` says the halves
cover `pZ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `split(pZ, gen)`: the two halves of the parallelotope along its generator `j`. -/
def PolyZonotope.split (pZ : PolyZonotope (Vec 𝕋 n)) (j : Fin pZ.splitParallelotope.h) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  ((pZ.splitParallelotope.split j).fst.polyZonotope,
    (pZ.splitParallelotope.split j).snd.polyZonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
