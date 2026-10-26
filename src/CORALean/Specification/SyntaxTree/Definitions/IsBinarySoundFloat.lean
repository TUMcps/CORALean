module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# A sound binary `funHan` over float intervals

`IsBinarySound` for the float intervals of `Float.SyntaxTree`: for a target `int` inside `v`, every
pair `s₁ ∈ prev₁`, `s₂ ∈ prev₂` with `f s₁ s₂ ∈ int` is held by the two intervals `funHan` returns,
each inside its operand's.

## Inputs
* `f` – binary function
* `prev₁` – first previous interval
* `prev₂` – second previous interval
* `v` – value interval
* `funHan` – backpropagation of the function

## Output
* the backpropagation keeps every solution inside the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `funHan` keeps every solution of `f s₁ s₂ ∈ int`, for a target `int` inside `v`. -/
def SyntaxTree.IsBinarySoundFloat (f : ℝ → ℝ → ℝ) (prev₁ prev₂ v : Float.SyntaxTree.Dom 𝕋)
    (funHan : Float.SyntaxTree.Dom 𝕋 → Float.SyntaxTree.Dom 𝕋 → Float.SyntaxTree.Dom 𝕋 →
      Float.SyntaxTree.Pair 𝕋) : Prop :=
  ∀ int : Float.SyntaxTree.Dom 𝕋, int.IsWithin v → ∀ s₁ s₂, prev₁.contains s₁ → prev₂.contains s₂ →
    int.contains (f s₁ s₂) →
      (funHan int prev₁ prev₂).left.contains s₁ ∧ (funHan int prev₁ prev₂).right.contains s₂ ∧
      (funHan int prev₁ prev₂).left.IsWithin prev₁ ∧ (funHan int prev₁ prev₂).right.IsWithin prev₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
