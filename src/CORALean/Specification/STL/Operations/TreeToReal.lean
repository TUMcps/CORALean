module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.ExprToReal
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# A syntax tree over a float scalar, read as reals

The tree whose numbers are the reals the stored ones denote and whose time bounds are the
nonnegative reals they denote (a negative bound reads as `0`, which CORA does not allow): what a
float `stl` formula means. The soundness of the float syntactic operations is stated through it.

## Inputs
* `φ` – formula

## Output
* the tree over `ℝ≥0` and `ℝ` with the denoted times and numbers
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

/-- The tree with the times and the numbers the stored ones denote. -/
noncomputable def STL.Tree.toReal (φ : STL.Tree 𝕋 𝕋 n) : STL.Tree NNReal ℝ n :=
  φ.map (fun a => Real.toNNReal (SoundFloatArithmetic.toReal a)) SoundFloatArithmetic.toReal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
