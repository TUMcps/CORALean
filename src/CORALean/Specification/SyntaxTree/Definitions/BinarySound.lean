module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# A sound binary `funHan`

The same for a binary node: for a target `int` inside `v`, every pair `s₁ ∈ prev₁`, `s₂ ∈ prev₂`
with
`f s₁ s₂ ∈ int` is held by the two intervals `funHan` returns, each inside its operand's.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `funHan` keeps every solution of `f s₁ s₂ ∈ int`, for a target `int` inside `v`. -/
def SyntaxTree.BinarySound (f : ℝ → ℝ → ℝ) (prev₁ prev₂ v : Dom)
    (funHan : Dom → Dom → Dom → Pair) : Prop :=
  ∀ int : Dom, Dom.within int v → ∀ s₁ s₂, Dom.contains prev₁ s₁ → Dom.contains prev₂ s₂ →
    Dom.contains int (f s₁ s₂) →
      Dom.contains (funHan int prev₁ prev₂).first s₁ ∧
      Dom.contains (funHan int prev₁ prev₂).second s₂ ∧
      Dom.within (funHan int prev₁ prev₂).first prev₁ ∧
      Dom.within (funHan int prev₁ prev₂).second prev₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
