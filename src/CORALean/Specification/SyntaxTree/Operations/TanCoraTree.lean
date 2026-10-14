module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.TanCora
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The tree `tan(x₁) - x₂`, with `tan` as printed

The leaves over `[0,π/3] × [0,2]`, combined as `tan(x₁) - x₂`: the tree of `tanCora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tree of `tan(x₁) - x₂` over `[0,π/3] × [0,2]`, with the printed `aux_tan_`. -/
noncomputable def SyntaxTree.tanCoraTree : SyntaxTree 2 :=
  .minus (.tanCora (.var 0 (interval 0 (Real.pi / 3)))) (.var 1 (interval 0 2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
