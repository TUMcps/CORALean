module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.TanCora
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The value of `tanCora`

The node `tanCora(obj)` builds denotes `tanCora` of the operand.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `tanCora(obj)` denotes tanCora of the operand. -/
theorem SyntaxTree.eval_tanCora (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.tanCora).eval x = Real.tan (t.eval x) := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
