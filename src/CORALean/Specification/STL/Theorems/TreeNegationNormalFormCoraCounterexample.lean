module

public import CORALean.Specification.STL.Operations.TreeNegationNormalFormCora

@[expose] public section

/-!
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
