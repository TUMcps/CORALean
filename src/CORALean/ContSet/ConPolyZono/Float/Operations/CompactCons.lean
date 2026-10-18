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
  let rt := PolyZonotope.repTab cPZ.R
  let kt := PolyZonotope.keepTab rt
  let r : Fin cPZ.q → Fin cPZ.q := fun l => rt.getD l.val l
  let k := PolyZonotope.tabAt (PolyZonotope.repKeep cPZ.R) kt
  let gap : Mat 𝕋 cPZ.m (PolyZonotope.repKeep cPZ.R).card := fun i l =>
    subUp (PolyZonotope.fiberUp r cPZ.A i (k l)) (PolyZonotope.fiberDown r cPZ.A i (k l))
  -- only the constraint block changes: its columns, the slack, and the count
  { p := cPZ.p
    h := cPZ.h
    qI := cPZ.qI
    m := cPZ.m
    q := (PolyZonotope.repKeep cPZ.R).card
    c := cPZ.c
    G := cPZ.G
    E := cPZ.E
    GI := cPZ.GI
    A := fun i l => PolyZonotope.fiberDown r cPZ.A i (k l)
    b := cPZ.b
    b_error := fun i => addUp (absolute (cPZ.b_error i)) (radius gap i)
    R := fun a l => cPZ.R a (k l)
    I_error := cPZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
