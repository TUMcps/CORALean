module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactorsSpec
public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt

@[expose] public section

/-!
# `ConPolyZono.compactFactors`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves.

The used factors are listed once, and every exponent read goes through that list:
the specification re-derives the sorted finset at each of the `p · (h + q)` reads
(issue #61). `compactFactors_eq_spec` says they are one.
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

/-- The factors neither block reads, dropped: `compactFactorsSpec` with the list of
used factors built once. -/
def ConPolyZono.compactFactors (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let ft := ((List.finRange cPZ.p).filter fun k =>
    (∃ i, Real.ConPolyZono.appendE cPZ.E cPZ.cons.R k i ≠ 0 : Bool)).toArray
  let f := PolyZonotope.tabAt (Real.ConPolyZono.usedFactors cPZ.E cPZ.cons.R) ft
  { p := (Real.ConPolyZono.usedFactors cPZ.E cPZ.cons.R).card
    h := cPZ.h
    qI := cPZ.qI
    c := cPZ.c
    G := cPZ.G
    E := fun k i => cPZ.E (f k) i
    GI := cPZ.GI
    cons := ⟨cPZ.cons.m, cPZ.cons.q, cPZ.cons.A, fun k l => cPZ.cons.R (f k) l, cPZ.cons.b,
      cPZ.cons.b_error, cPZ.cons.op⟩
    cons_eq := cPZ.cons_eq
    I_error := cPZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
