module

public import CORALean.Specification.STL.Definitions.Shift
public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# The `release` node of float bounds, read as reals

The `release` node `φ R[a,b] ψ` of CORA's syntax tree stores its bounds as given, so read as reals
it holds of a trace iff there is no time in the bounds read as nonnegative reals at which `ψ` fails
with `φ` failing at every step up to and including it.

## Inputs
* `a` – lower bound
* `b` – upper bound
* `φ` – left formula
* `ψ` – right formula
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

theorem STL.Tree.sat_release_toReal (a b : 𝕋) (φ ψ : STL.Tree 𝕋 𝕋 n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.release a b φ ψ).toReal.Satisfies ξ ↔
      ¬ ∃ t, Real.toNNReal (SoundFloatArithmetic.toReal a) ≤ t ∧
        t ≤ Real.toNNReal (SoundFloatArithmetic.toReal b) ∧
        ¬ ψ.toReal.Satisfies (Time.shift ξ t) ∧ ∀ t' ≤ t, ¬ φ.toReal.Satisfies (Time.shift ξ t') :=
  Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
