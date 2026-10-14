module

public import CORALean.Specification.STL.Operations.TreeNnfWith
public import CORALean.Specification.STL.Operations.CmpDual

@[expose] public section

/-!
# CORA's `negationNormalForm`, as printed

`@stl/negationNormalForm.m` turns `~(x < 5)` into `x > 5` (`obj.lhs > obj.rhs`), `~(x > 5)` into
`x < 5`, `~(x <= 5)` into `x >= 5` and `~(x >= 5)` into `x <= 5`: the sides swap and the
strictness stays, so the result differs from the formula at the boundary (`x = 5`). The result is
not equivalent to the argument; `STL.Tree.negationNormalFormCora_counterexample` is a trace where
it differs, and `STL.Tree.negationNormalForm` the version with `Cmp.negate`.

# CORA's `negationNormalForm` changes the meaning at a boundary

`negationNormalForm(~(x < 0))` is `x > 0` (`obj.lhs > obj.rhs`), not `x >= 0`: at `x = 0` the
argument holds and the result does not. See `STL.Tree.negationNormalFormCora`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `negationNormalForm(obj)`, `aux_recursive(obj,false)`, as printed. -/
def STL.Tree.negationNormalFormCora (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.nnfWith STL.Cmp.dual false φ

end CORALean

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.negationNormalFormCora_counterexample :
    ∃ (φ : STL.Tree 1) (ξ : ℝ≥0 → Fin 1 → ℝ),
      ¬ (φ.negationNormalFormCora.Sat ξ ↔ φ.Sat ξ) := by
  refine ⟨.not (.cmp .lt (.var 0) (.num 0)), fun _ _ => 0, ?_⟩
  simp [STL.Tree.negationNormalFormCora, STL.Tree.nnfWith, STL.Cmp.dual, STL.Tree.Sat,
    STL.Expr.eval, STL.Cmp.rel]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
