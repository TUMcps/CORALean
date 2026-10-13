import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Real.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

/-!
# `ConPolyZono.linComb`

CORA's `@conPolyZono/linComb`: `PolyZonotope.linComb` on the generators — which
is where the fresh factor for the segment parameter comes from — with the two
constraint systems carried along side by side, `plusA` and `plusB` as `plus`
lays them out, and `padE` giving the fresh factor a row of zeros.

Both systems are imposed unconditionally, and that is not an approximation: a
point of `linComb` is `λ x₁ + (1-λ) x₂`, so *both* operands contribute to
*every* point of it and there is no conditionality to express. After the
`linComb` the two factor groups are disjoint, so the two systems constrain
disjoint variables and are satisfiable independently.

At `λ = 0` the first operand's point drops out while its constraints stay. That
changes nothing unless it is empty — and then the combination is empty too,
which is the answer wanted.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConPolyZono.linComb (cPZ₁ cPZ₂ : ConPolyZono α) : ConPolyZono α :=
  let pZ := cPZ₁.toPolyZonotope.linComb cPZ₂.toPolyZonotope   -- the segment's generators
  { p := cPZ₁.p + cPZ₂.p + 1
    h := cPZ₁.h + cPZ₂.h + (cPZ₁.h + cPZ₂.h + 1)
    q := cPZ₁.q + cPZ₂.q
    m := cPZ₁.m + cPZ₂.m
    s := cPZ₁.s + cPZ₂.s
    c := pZ.c
    G := pZ.G
    E := pZ.E
    GI := pZ.GI
    A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
    b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
    EC := ConPolyZono.padE (PolyZonotope.plusE cPZ₁.EC cPZ₂.EC) 1 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
