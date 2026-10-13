module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Isequal

@[expose] public section

/-!
# `ZonoBundle.isequal`, over a floating-point scalar

The quick check at tolerance `0`, as over ℝ: the same number of members, and every member pair
`Zonotope.isequal`. Certified in one direction only: `true` is a proof, `false` refutes nothing.
Not CORA's test, whose mutual-containment step is not modelled, and which answers `true` for
different member counts (see `ZonoBundle.isequalCora`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.isequal (zB S : ZonoBundle (Vec 𝕋 n)) : Bool :=
  if e : zB.k = S.k then
    (List.finRange zB.k).all fun i => Zonotope.isequal (zB.Z i) (S.Z (Fin.cast e i))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
