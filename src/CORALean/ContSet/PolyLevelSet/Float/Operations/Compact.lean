module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.CompactSpec
public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab

@[expose] public section

/-!
# `PolyLevelSet.compact` over a floating-point scalar

Equal exponent columns merged, as `Real.PolyLevelSet.compact` does, the stored coefficients the
lower rounding and the widening paid into the slack `b_error`. No zero test is made, costing a
column that denotes nothing rather than soundness. The exponent matrix is scanned once, as
`PolyZonotope.compactGens`' is, and every entry read through the tables; `compact_eq_spec` says
this is `compactSpec` (issue #61). The widening holds on the unit box, where every monomial is in
`[-1,1]` (`mem_compact_of_mem`).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's merge of equal exponent columns, as computed: `compactSpec` with the representative
and kept-column lookups shared between entries. -/
def PolyLevelSet.compact (P : PolyLevelSet 𝕋 n) : PolyLevelSet 𝕋 n :=
  let rt := PolyZonotope.repTab P.R
  let kt := PolyZonotope.keepTab rt
  let r : Fin P.q → Fin P.q := fun l => rt.getD l.val l
  let k := PolyZonotope.tabAt (PolyZonotope.repKeep P.R) kt
  let gap : Mat 𝕋 P.m (PolyZonotope.repKeep P.R).card := fun i l =>
    subUp (PolyZonotope.fiberUp r P.A i (k l)) (PolyZonotope.fiberDown r P.A i (k l))
  ⟨P.m, (PolyZonotope.repKeep P.R).card, fun i l => PolyZonotope.fiberDown r P.A i (k l),
    fun a l => P.R a (k l), P.b, fun i => addUp (absolute (P.b_error i)) (radius gap i), P.op,
    P.dom⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
