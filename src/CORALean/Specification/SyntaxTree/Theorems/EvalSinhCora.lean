module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.SinhCora
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The value of `sinhCora`

The node `sinhCora(obj)` builds denotes `sinhCora` of the operand.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sinhCora(obj)` denotes sinhCora of the operand. -/
theorem SyntaxTree.eval_sinhCora (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.sinhCora).eval x = Real.sinh (t.eval x) := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
