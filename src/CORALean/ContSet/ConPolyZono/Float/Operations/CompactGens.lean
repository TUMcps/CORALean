module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensSpec
public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# `ConPolyZono.compactGens`

Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the ambient box. The constraint block stands.

The exponent matrix is scanned once, into a table of representatives and a table
of kept columns, and every entry is read through those: the specification
`compactGensSpec` rescans for each of the `n · h` entries and each of the `h`
summands under it (issue #61). `compactGens_eq_spec` says they are one.
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

/-- CORA's merge of equal exponent columns, as computed: `compactGensSpec` with
the representative and kept-column lookups shared between entries. -/
def ConPolyZono.compactGens (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let rt := PolyZonotope.repTab cPZ.E
  let kt := PolyZonotope.keepTab rt
  let r : Fin cPZ.h → Fin cPZ.h := fun l => rt.getD l.val l
  let k := PolyZonotope.tabAt (PolyZonotope.repKeep cPZ.E) kt
  { p := cPZ.p
    h := (PolyZonotope.repKeep cPZ.E).card
    q := cPZ.q
    m := cPZ.m
    s := cPZ.s
    c := cPZ.c
    G := fun j i => PolyZonotope.fiberDown r (fun i l => cPZ.G l i) i (k j)
    E := fun a j => cPZ.E a (k j)
    GI := cPZ.GI
    A := cPZ.A
    b := cPZ.b
    EC := cPZ.EC
    I_error := cPZ.I_error.plus (PolyZonotope.generatorError fun i j =>
      subUp (PolyZonotope.fiberUp r (fun i l => cPZ.G l i) i (k j))
        (PolyZonotope.fiberDown r (fun i l => cPZ.G l i) i (k j))) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
