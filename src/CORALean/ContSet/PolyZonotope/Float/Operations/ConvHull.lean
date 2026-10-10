import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Operations.NoIndep
import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# `PolyZonotope.convHull`, over a floating-point scalar

CORA's `@polyZonotope/convHull_` for a second polynomial zonotope, as over ℝ: the dependent parts
paired with themselves by `linComb`, those chord sets with each other, and the independent
generators of the result taken from `enclose(Z1, Z2)` of the zero-centred zonotopes of the two
independent blocks (`Zonotope.linComb`).

The zonotope's rounded centre is not a generator, so it enters the error box as a point, with the
zonotope's own error box: the generators `Z.G` replace the independent block and `Z.c` and `Z.E`
widen the error.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.convHull (pZ₁ pZ₂ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n :=
  -- pZ1_ = polyZonotope(pZ1.c, pZ1.G, [], pZ1.E, pZ1.id), and pZ2_ likewise
  let pZ₁' := pZ₁.noIndep
  let pZ₂' := pZ₂.noIndep
  -- pZ = linComb(linComb(pZ1_, pZ1_), linComb(pZ2_, pZ2_))
  let pZ := (pZ₁'.linComb pZ₁').linComb (pZ₂'.linComb pZ₂')
  -- Z1 = zonotope(c0, pZ1.GI), Z2 = zonotope(c0, S.GI)
  let Z₁ : Zonotope 𝕋 n := ⟨pZ₁.q, fun _ => zero, fun j i => pZ₁.GI i j, Interval.origin n⟩
  let Z₂ : Zonotope 𝕋 n := ⟨pZ₂.q, fun _ => zero, fun j i => pZ₂.GI i j, Interval.origin n⟩
  -- Z = enclose(Z1, Z2)
  let Z := Z₁.linComb Z₂
  -- pZ.GI = Z.G
  { pZ with q := Z.h, GI := fun i j => Z.G j i, err := pZ.err.plus (Z.E.plus (Interval.point Z.c)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
