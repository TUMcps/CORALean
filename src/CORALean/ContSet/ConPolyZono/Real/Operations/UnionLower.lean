module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerR
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionLower`

The lower rows of [1, Thm. 1] as a polynomial level set on the union's factors: each operand's own
equations on its own factors, every row shifted by its right-hand side times the selector factor,
so that it binds on its own branch and falls away on the other (`unionLowerA`, `unionLowerR`,
`unionLowerB`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p₁ p₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both operands' equations, switched by the selector factor. -/
noncomputable def ConPolyZono.unionLower (P₁ : PolyLevelSet p₁) (P₂ : PolyLevelSet p₂) :
    PolyLevelSet (p₁ + p₂ + 2) :=
  ⟨P₁.m + P₂.m, P₁.q + P₂.q + 1, ConPolyZono.unionLowerA P₁.A P₁.b P₂.A P₂.b,
    ConPolyZono.unionLowerR P₁.R P₂.R, ConPolyZono.unionLowerB P₁.b P₂.b, fun _ => .eq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
