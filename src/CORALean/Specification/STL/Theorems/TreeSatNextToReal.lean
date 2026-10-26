module

public import CORALean.Specification.STL.Definitions.Shift
public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# The `next` node of a float shift, read as reals

The `next` node `X_a φ` of CORA's syntax tree stores its shift as given, so read as reals it holds
of a trace iff `φ` holds of the trace shifted by the nonnegative real the shift denotes.

## Inputs
* `a` – time shift
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the node holds of a trace iff `φ` holds of the shifted trace
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

open scoped NNReal

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_next_toReal (a : 𝕋) (φ : STL.Tree 𝕋 𝕋 n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.next a φ).toReal.Satisfies ξ ↔
      φ.toReal.Satisfies (Time.shift ξ (Real.toNNReal (SoundFloatArithmetic.toReal a))) :=
  Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
