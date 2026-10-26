module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Specification.STL.Operations.ExprMap

@[expose] public section

/-!
# An expression over a float scalar, read as reals

The expression whose numbers are the reals the stored ones denote: what a float `stl` expression
means. The soundness of the float syntactic operations is stated through it.

## Inputs
* `e` – expression

## Output
* the expression over `ℝ` with the denoted numbers
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The expression with the reals its numbers denote. -/
noncomputable def STL.Expr.toReal (e : STL.Expr 𝕋 n) : STL.Expr ℝ n := e.map
  SoundFloatArithmetic.toReal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
