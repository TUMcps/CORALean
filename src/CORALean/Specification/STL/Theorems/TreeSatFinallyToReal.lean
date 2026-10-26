module

public import CORALean.Specification.STL.Definitions.Shift
public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# The `finally` node of float bounds, read as reals

The `finally` node `F[a,b] φ` of CORA's syntax tree stores its bounds as given, so read as reals it
holds of a trace iff `φ` holds at some time in the bounds read as nonnegative reals.

## Inputs
* `a` – lower bound
* `b` – upper bound
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the node holds of a trace iff the clause holds, the bounds read as the nonnegative reals they
  denote
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

theorem STL.Tree.sat_finally_toReal (a b : 𝕋) (φ : STL.Tree 𝕋 𝕋 n)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (STL.Tree.finally a b φ).toReal.Satisfies ξ ↔
      ∃ t, Real.toNNReal (SoundFloatArithmetic.toReal a) ≤ t ∧
        t ≤ Real.toNNReal (SoundFloatArithmetic.toReal b) ∧
          φ.toReal.Satisfies (Time.shift ξ t) := by -- --- PROOF ---
  simp [STL.Tree.toReal, STL.Tree.map, STL.Tree.Satisfies, STL.Tree.HasUntilWitness]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
