module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsSpec
public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab

@[expose] public section

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into the slack `b_error`. The generators stand, so the ambient
box is untouched.

The constraint exponent matrix is scanned once, as `compactGens`' is, and every
entry read through the tables; `compactCons_eq_spec` says this is
`compactConsSpec` (issue #61).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's merge of equal constraint columns, as computed: `compactConsSpec` with
the representative and kept-column lookups shared between entries. -/
def ConPolyZono.compactCons (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let rt := PolyZonotope.repTab cPZ.cons.R
  let kt := PolyZonotope.keepTab rt
  let r : Fin cPZ.cons.q → Fin cPZ.cons.q := fun l => rt.getD l.val l
  let k := PolyZonotope.tabAt (PolyZonotope.repKeep cPZ.cons.R) kt
  let gap : Mat 𝕋 cPZ.cons.m (PolyZonotope.repKeep cPZ.cons.R).card := fun i l =>
    subUp (PolyZonotope.fiberUp r cPZ.cons.A i (k l)) (PolyZonotope.fiberDown r cPZ.cons.A i (k l))
  -- only the constraint block changes: its columns, the slack, and the count
  { p := cPZ.p
    h := cPZ.h
    qI := cPZ.qI
    c := cPZ.c
    G := cPZ.G
    E := cPZ.E
    GI := cPZ.GI
    cons := ⟨cPZ.cons.m, (PolyZonotope.repKeep cPZ.cons.R).card,
      fun i l => PolyZonotope.fiberDown r cPZ.cons.A i (k l), fun a l => cPZ.cons.R a (k l),
      cPZ.cons.b, fun i => addUp (absolute (cPZ.cons.b_error i)) (radius gap i), cPZ.cons.op⟩
    cons_eq := cPZ.cons_eq
    I_error := cPZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
