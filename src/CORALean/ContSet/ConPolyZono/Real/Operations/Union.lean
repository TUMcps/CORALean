module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionG
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLower
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.union`

CORA's `@conPolyZono/or`, and [1, Thm. 1]: the closed form for the union of two
constrained polynomial zonotopes. Two fresh factors and two constraint rows cut
the factor cube down to two disjoint branches — one pinning the second operand's
factors to `0`, one pinning the first's — and on each branch what is left is the
operand the branch selects.

No independent generators: [1, Def. 5] has none, and there is nothing for them to
mean here, a coefficient answering to no constraint being free on both branches.

The result is not regular, and CORA follows the closed form with `compact_`;
`compactGens` and `compactCons` are that, and are not applied here.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union, as one constrained polynomial zonotope. -/
noncomputable def ConPolyZono.union {α : Type} [AddCommGroup α] [Module ℝ α]
    (cPZ₁ cPZ₂ : ConPolyZono α) : ConPolyZono α where
  p := cPZ₁.p + cPZ₂.p + 2
  h := 1 + (cPZ₁.h + cPZ₂.h)
  qI := 0
  c := (2 : ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
  G := ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G
  E := ConPolyZono.unionE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  cons := (ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).and_ (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons)
  cons_eq := LevelSet.append_op_eq (LevelSet.append_op_eq (fun _ => rfl) fun _ => rfl)
    (LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
