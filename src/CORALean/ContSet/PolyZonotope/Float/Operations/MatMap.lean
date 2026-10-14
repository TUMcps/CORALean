module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinE
public import CORALean.ContSet.PolyZonotope.Float.Operations.MatGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.PairG
public import CORALean.ContSet.PolyZonotope.Float.Operations.PairGI

@[expose] public section

/-!
# `PolyZonotope.matMap`, over a floating-point scalar

CORA's `matMap(pZ1, pZ2, n, k, m)` as `Real.PolyZonotope.matMap` has it — `bilin` at matrix
multiplication over shared factors, plus the independent cross terms — with every product of two
generators stored rounded down (`matMulDown`) and the gap to the upper rounding charged to the
error box. The operands' own error boxes enter by interval-matrix products against hulls of the
operands: `(N₁ + e₁)(N₂ + e₂) = N₁N₂ + N₁e₂ + e₁(N₂ + e₂)`, `N` bounded entrywise by the sum
of its generators' absolute values.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.matMap (pZ₁ : PolyZonotope (Mat 𝕋 n k)) (pZ₂ : PolyZonotope (Mat 𝕋 k m))
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (Mat 𝕋 n m) :=
  -- the rounding of every stored product, dependent then independent
  let gap := PolyZonotope.matGeneratorError
    (Fin.append (PolyZonotope.pairG matMulDiff pZ₁ pZ₂) (PolyZonotope.pairGI matMulDiff pZ₁ pZ₂))
  -- the operands' hulls: every generator, centre included, at a coefficient in `[-1, 1]`
  let H₁ := PolyZonotope.matGeneratorError (Fin.append (PolyZonotope.extGens pZ₁) pZ₁.GI)
  let H₂ := PolyZonotope.matGeneratorError (Fin.append (PolyZonotope.extGens pZ₂) pZ₂.GI)
  -- the operands' error boxes: `N₁ e₂ + e₁ (N₂ + e₂)`
  let errs := Interval.matPlus (Interval.matMul H₁ pZ₂.I_error)
    (Interval.matMul pZ₁.I_error (Interval.matPlus H₂ pZ₂.I_error))
  { p := pZ₁.p
    h := (pZ₁.h + 1) * (pZ₂.h + 1)
    q := pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q
    c := fun _ _ => zero
    G := PolyZonotope.pairG matMulDown pZ₁ pZ₂
    E := PolyZonotope.bilinE pZ₁ pZ₂ hp
    GI := PolyZonotope.pairGI matMulDown pZ₁ pZ₂
    I_error := Interval.matPlus gap errs }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
