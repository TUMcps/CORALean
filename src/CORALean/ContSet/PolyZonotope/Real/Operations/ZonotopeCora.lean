import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraWeight

/-!
# `PolyZonotope.zonotopeCora`

CORA's `@polyZonotope/zonotope` as it is written: every dependent generator is scaled by its
`coraWeight`, the rest of it moved into the centre, and the independent generators appended.
A constant column costs a half generator there; `PolyZonotope.zonotopeEven` frees none of it,
so this is the conversion the callers that reduce the result (`containsPointSet`) have to use
to match CORA, a reduction not being monotone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.zonotopeCora (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c + ∑ i, (1 - PolyZonotope.coraWeight pZ.E i) • pZ.G i
  G := Fin.append (fun i => PolyZonotope.coraWeight pZ.E i • pZ.G i) pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
