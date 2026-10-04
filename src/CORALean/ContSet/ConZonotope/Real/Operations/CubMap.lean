import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Operations.CubLinearAt
import CORALean.ContSet.Zonotope.Real.Operations.CubMap
import CORALean.ContSet.HPolytope.Real.Operations.Comap

/-!
# `ConZonotope.cubMap`

CORA's `@conZonotope/cubMap` (`aux_cubMapSingle`): the generators of `Zonotope.cubMap` on the centre
and generators, with the constraint `A β = b` kept on the *linear* monomials, the generators
`(0, 0, j)` whose factor is the old `βⱼ`, and every other monomial factor (`βⱼβₖ`, `2βⱼ² - 1`, the
cubes, ...) unconstrained. CORA reaches this through the polynomial zonotope `cubMap` of
`polyZonotope(zonotope(c, G))`, reading the linear monomials off its exponent matrix.

**Where this differs from CORA.** That route runs `removeRedundantExponents`, which drops every
generator column that is zero in all outputs. A linear monomial whose coefficient vanishes (a factor
the cubic map does not depend on) disappears, and with it that factor's column of the constraint
matrix: `A β = b` is imposed on the remaining factors alone, which is unsound
(`ConZonotope.cubMapCora_not_outer`, `FINDINGS.md`). Here every linear generator is kept, zero or
not, as the single-set `quadMap` does. `rescale` (it only tightens) and `ind` are not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
