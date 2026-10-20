module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.CubLinearAt
public import CORALean.ContSet.Zonotope.Real.Operations.CubMap
public import CORALean.ContSet.HPolytope.Real.Operations.Comap

@[expose] public section

/-!
# `ConZonotope.cubMap`

CORA's `@conZonotope/cubMap` (`aux_cubMapSingle`): the generators of `Zonotope.cubMap`, with
`A β = b` kept on the *linear* monomials (the generators `(0, 0, j)`, factor `βⱼ`) and every other
factor unconstrained. CORA reaches this through the polynomial zonotope `cubMap`.

**Where this differs from CORA.** That route runs `removeRedundantExponents`, which drops a linear
monomial whose coefficient vanishes, and with it that factor's column of `A`, so `A β = b` is
imposed on the remaining factors alone: unsound (`ConZonotope.cubMapCora_not_outer`). Here every
linear generator is kept, as the single-set `quadMap` does; `rescale` and `ind` are not modelled.

## Inputs
* `T` – cubic map tensor
* `cZ` – constrained zonotope

## Output
* enclosure of the cubic image
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cubMapSingle`: `Z.cubMap T` with the constraints on the linear monomials. -/
noncomputable def ConZonotope.cubMap (T : Fin m → Fin n → Mat ℝ n n) (cZ : ConZonotope (Vec ℝ n)) :
    ConZonotope (Vec ℝ m) :=
  let Z : Zonotope (Vec ℝ n) := ⟨cZ.h, cZ.c, cZ.G⟩
  { h := (Z.cubMap T).h
    c := (Z.cubMap T).c
    G := (Z.cubMap T).G
    P := cZ.P.comap (ConZonotope.cubLinearAt (cZ.h + 1) (cZ.h + 1) (cZ.h + 1)
      (fun j : Fin cZ.h => ((0, 0), j.succ))) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
