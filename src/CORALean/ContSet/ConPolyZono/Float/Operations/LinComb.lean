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

CORA's `@conPolyZono/linComb`, as the exact layer lays it out: the float
`PolyZonotope.linComb` on the generators, which is where the fresh factor for the
segment parameter comes from and where every rounding is paid, with the two
constraint systems carried along side by side.

The constraint side computes nothing: it is the float `PolyLevelSet.cartProd` of the two, which
places the matrices block-diagonally with `zero` off the blocks and stacks `b` and `b_error`,
padded with the fresh factor (`PolyLevelSet.padVars`), so the constraints of the result are
exactly the two operands' — read on the factors they came with, the fresh one at exponent zero. The
error box is therefore the generator part's, unchanged.
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
