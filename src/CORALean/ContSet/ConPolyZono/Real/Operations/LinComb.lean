module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

@[expose] public section

/-!
# `ConPolyZono.linComb`

CORA's `@conPolyZono/linComb`: `PolyZonotope.linComb` on the generators — which
is where the fresh factor for the segment parameter comes from — with the two
constraint systems carried along side by side, `PolyLevelSet.cartProd` as `plus`
lays them out, and `PolyLevelSet.padVars` giving the fresh factor a row of zeros.

Both systems are imposed unconditionally, and that is not an approximation: a
point of `linComb` is `λ x₁ + (1-λ) x₂`, so *both* operands contribute to
*every* point of it and there is no conditionality to express. After the
`linComb` the two factor groups are disjoint, so the two systems constrain
disjoint variables and are satisfiable independently.

At `λ = 0` the first operand's point drops out while its constraints stay. That
changes nothing unless it is empty — and then the combination is empty too,
which is the answer wanted.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConPolyZono.linComb (cPZ₁ cPZ₂ : ConPolyZono α) : ConPolyZono α :=
  let pZ := cPZ₁.toPolyZonotope.linComb cPZ₂.toPolyZonotope   -- the segment's generators
  { p := cPZ₁.p + cPZ₂.p + 1
    h := cPZ₁.h + cPZ₂.h + (cPZ₁.h + cPZ₂.h + 1)
    qI := cPZ₁.qI + cPZ₂.qI
    c := pZ.c
    G := pZ.G
    E := pZ.E
    GI := pZ.GI
    cons := (cPZ₁.cons.cartProd cPZ₂.cons).padVars (Interval.unit 1)
    cons_eq := LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
    cons_dom := Interval.append_eq_unit (Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom) rfl }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
