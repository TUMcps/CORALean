module

public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.linComb`

CORA's `@conPolyZono/linComb`: the float `PolyZonotope.linComb` on the generators, which is where
the fresh factor for the segment parameter comes from and where every rounding is paid, with the
two constraint systems carried along side by side.

The constraint side computes nothing: it is the float `PolyLevelSet.cartProd` of the two, padded
with the fresh factor (`PolyLevelSet.padVars`), so the error box is the generator part's,
unchanged.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* linear combination of the two sets
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.linComb (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let pZ := cPZ₁.polyZonotope.linComb cPZ₂.polyZonotope   -- the segment's generators
  { p := cPZ₁.p + cPZ₂.p + 1
    h := cPZ₁.h + cPZ₂.h + (cPZ₁.h + cPZ₂.h + 1)
    qI := cPZ₁.qI + cPZ₂.qI
    c := pZ.c
    G := pZ.G
    E := pZ.E
    GI := pZ.GI
    cons := (cPZ₁.cons.cartProd cPZ₂.cons).padVars (Interval.unit 1)
    cons_eq := Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
    cons_dom := Interval.append_eq_unit (Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom) rfl
    I_error := pZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
