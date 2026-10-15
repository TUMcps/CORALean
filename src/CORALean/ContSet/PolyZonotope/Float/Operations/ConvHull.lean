module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
public import CORALean.ContSet.PolyZonotope.Float.Operations.NoIndep
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb

@[expose] public section

/-!
# `PolyZonotope.convHull`, over a floating-point scalar

CORA's `@polyZonotope/convHull_` for a second polynomial zonotope, as over ℝ: the dependent parts
paired with themselves by `linComb`, those chord sets with each other, and the independent
generators of the result taken from `enclose(Z1, Z2)` of the zero-centered zonotopes of the two
independent blocks (`Zonotope.linComb`).

The zonotope's rounded center is not a generator, so it enters the error box as a point, with the
zonotope's own error box: the generators `Z.G` replace the independent block and `Z.c` and `Z.E`
widen the error.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.convHull (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  -- pZ1_ = polyZonotope(pZ1.c, pZ1.G, [], pZ1.E, pZ1.id), and pZ2_ likewise
  let pZ₁' := pZ₁.noIndep
  let pZ₂' := pZ₂.noIndep
  -- pZ = linComb(linComb(pZ1_, pZ1_), linComb(pZ2_, pZ2_))
  let pZ := (pZ₁'.linComb pZ₁').linComb (pZ₂'.linComb pZ₂')
  -- Z1 = zonotope(c0, pZ1.GI), Z2 = zonotope(c0, S.GI)
  let Z₁ : Zonotope (Vec 𝕋 n) := ⟨pZ₁.q, fun _ => zero, pZ₁.GI, Interval.origin n⟩
  let Z₂ : Zonotope (Vec 𝕋 n) := ⟨pZ₂.q, fun _ => zero, pZ₂.GI, Interval.origin n⟩
  -- Z = enclose(Z1, Z2)
  let Z := Z₁.linComb Z₂
  -- pZ.GI = Z.G
  { pZ with q := Z.h, GI := Z.G, I_error := pZ.I_error.plus (Z.I_error.plus (Interval.point Z.c)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
