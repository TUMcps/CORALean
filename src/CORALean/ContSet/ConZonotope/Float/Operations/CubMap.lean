module

public import CORALean.ContSet.ConZonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.Zonotope.Float.Operations.CubMapDep

@[expose] public section

/-!
# `ConZonotope.cubMap`, over a floating-point scalar

CORA's `@conZonotope/cubMap` (`aux_cubMapSingle`) for a single constrained zonotope on the stored
floats: the error box made into coefficients (`absorbRounding`), then the generators of
`Zonotope.cubMapDep` on the center and generators, with the constraints kept on the *linear*
monomials, the generators `(0, 0, j)` whose factor is the old `βⱼ`, and every other monomial factor
(`βⱼβₖ`, `2βⱼ² - 1`, the cubes, ...) unconstrained: `lift_` writes the operand's constraints on
those coordinates. Every linear generator is kept, zero or not, where CORA's
`removeRedundantExponents` drops the zero ones with their constraint columns
(`Real.ConZonotope.cubMapCora_not_outer`). `rescale` (it only tightens) and `ind` are not
modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.cubMap (T : Fin m → Fin n → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    ConZonotope 𝕋 (Vec 𝕋 m) :=
  let d := cZ.absorbRounding
  -- the zonotope `Zonotope.cubMapDep` maps
  let Z : Zonotope (Vec 𝕋 n) := ⟨d.h, d.c, d.G, d.I_error⟩
  { h := (Zonotope.cubMapDep T Z).h
    c := (Zonotope.cubMapDep T Z).c
    G := (Zonotope.cubMapDep T Z).G
    P := d.P.lift_ fun j : Fin d.h =>
      (Real.Zonotope.cubIdx (d.h + 1) (d.h + 1) (d.h + 1)).symm ((0, 0), j.succ)
    I_error := (Zonotope.cubMapDep T Z).I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
