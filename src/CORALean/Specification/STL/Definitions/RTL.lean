module

public import CORALean.Specification.STL.Definitions.Pform
public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# Reachset temporal logic

[1, Def. 1] and [1, Def. 2]: `ψ := Aϱ | ψ₁ ∧ ψ₂ | ψ₁ ∨ ψ₂ | Xₐψ | ψ₁ U[a,b] ψ₂ | ψ₁ R[a,b] ψ₂`,
negation only inside `ϱ`, and `R ⊨ᵣ ψ` for a reach sequence `R : ℝ≥0 → Set X`, Eqs. (4)-(9).

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A reachset temporal logic formula: a propositional formula, conjunction, disjunction, next,
until and release. -/
inductive RTL.Formula (X : Type)
  | A (ϱ : Pform X)
  | and (ψ₁ ψ₂ : Formula X)
  | or (ψ₁ ψ₂ : Formula X)
  | next (a : ℝ≥0) (ψ : Formula X)
  | until (a b : ℝ≥0) (ψ₁ ψ₂ : Formula X)
  | release (a b : ℝ≥0) (ψ₁ ψ₂ : Formula X)

/-- `R ⊨ᵣ ψ`, [1, Def. 2], Eqs. (4)-(9). -/
def RTL.Formula.Satisfies : RTL.Formula X → (ℝ≥0 → Set X) → Prop
  | .A ϱ, R => ∀ r ∈ R 0, ϱ.Satisfies r
  | .and ψ₁ ψ₂, R => ψ₁.Satisfies R ∧ ψ₂.Satisfies R
  | .or ψ₁ ψ₂, R => ψ₁.Satisfies R ∨ ψ₂.Satisfies R
  | .next a ψ, R => ψ.Satisfies (Time.shift R a)
  | .until a b ψ₁ ψ₂, R =>
      ∃ t, a ≤ t ∧ t ≤ b ∧ ψ₂.Satisfies (Time.shift R t) ∧ ∀ i < t, ψ₁.Satisfies (Time.shift R i)
  | .release a b ψ₁ ψ₂, R =>
      ∀ t, a ≤ t → t ≤ b → ψ₂.Satisfies (Time.shift R t) ∨ ∃ i < t, ψ₁.Satisfies (Time.shift R i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
