module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsSpec
public import CORALean.ContSet.PolyZonotope.Float.Operations.FiberUp
public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab

@[expose] public section

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched.

The constraint exponent matrix is scanned once, as `compactGens`' is, and every
entry read through the tables; `compactCons_eq_spec` says this is
`compactConsSpec` (issue #61).
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   11-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's merge of equal constraint columns, as computed: `compactConsSpec` with
the representative and kept-column lookups shared between entries. -/
def ConPolyZono.compactCons (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let rt := PolyZonotope.repTab cPZ.EC
  let kt := PolyZonotope.keepTab rt
  let r : Fin cPZ.s → Fin cPZ.s := fun l => rt.getD l.val l
  let k := PolyZonotope.tabAt (PolyZonotope.repKeep cPZ.EC) kt
  let gap : Mat 𝕋 cPZ.m (PolyZonotope.repKeep cPZ.EC).card := fun i l =>
    subUp (PolyZonotope.fiberUp r cPZ.A i (k l)) (PolyZonotope.fiberDown r cPZ.A i (k l))
  -- only the constraint block changes: its columns, `b`, and the count
  { p := cPZ.p
    h := cPZ.h
    q := cPZ.q
    m := cPZ.m
    s := (PolyZonotope.repKeep cPZ.EC).card
    c := cPZ.c
    G := cPZ.G
    E := cPZ.E
    GI := cPZ.GI
    A := fun i l => PolyZonotope.fiberDown r cPZ.A i (k l)
    b := ⟨fun i => subDown (cPZ.b.inf i) (radius gap i),
      fun i => addUp (cPZ.b.sup i) (radius gap i)⟩
    EC := fun a l => cPZ.EC a (k l)
    err := cPZ.err }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
