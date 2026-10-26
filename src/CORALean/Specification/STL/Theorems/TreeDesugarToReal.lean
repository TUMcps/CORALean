module

public import CORALean.Specification.STL.Operations.TreeDesugar
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `desugar` of a float syntax tree, read as reals

`desugar` rewrites `release`, `finally`, `globally` and `next` to `until` and `~` and reads no time
or number, so the desugared tree read as reals is the desugaring of the tree read as reals.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the result read as reals is the operation on the argument read as reals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.desugar_toReal (φ : STL.Tree 𝕋 𝕋 n) : φ.desugar.toReal = φ.toReal.desugar := by
  induction φ <;> simp_all [STL.Tree.desugar, STL.Tree.toReal, STL.Tree.map]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
