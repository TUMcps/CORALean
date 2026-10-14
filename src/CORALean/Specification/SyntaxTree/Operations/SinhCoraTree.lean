module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.SinhCora
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The tree `sinh(x₁) - x₂`, with `sinh` as printed

`syntaxTree(dom(1))` and `syntaxTree(dom(2))` over `[0,3] × [0,3/2]`, combined as `sinh(x₁) - x₂`:
the
function `contractForwardBackward` is given in `sinhCora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tree of `sinh(x₁) - x₂` over `[0,3] × [0,3/2]`, with the printed `aux_sinh_`. -/
noncomputable def SyntaxTree.sinhCoraTree : SyntaxTree 2 :=
  .minus (.sinhCora (.var 0 (interval 0 3))) (.var 1 (interval 0 (3 / 2)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
