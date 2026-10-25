module

public import CORALean.Specification.STL.Definitions.Pform
public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# Signal temporal logic

[1, Sec. 2.2]: `φ := p | ¬φ | φ₁ ∨ φ₂ | φ₁ U[a,b] φ₂` over traces `ξ : ℝ≥0 → X`, and
`ξ ⊨ₜ φ` by the printed recursion. `finOpen` and `globOpen` are the operators `F(0,c)` and
`G(0,c)` of [1, Sec. 4.1], which the paper writes over an open interval, with the semantics
`∃t ∈ (0,c)` and `∀t ∈ (0,c)` the closed-interval `U` cannot express.

A formula is a Lean value over `X`, not over a name set `AP`: see `Pform`. The derived
operators are definitions, `release` the dual of `until` that [1, Lemma 4] uses.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A signal temporal logic formula: an atomic predicate, negation, disjunction, until, and the
open-interval finally and globally of the sampled-time rewriting. -/
inductive STL.Formula (X : Type)
  | atom (p : X → Prop)
  | not (φ : Formula X)
  | or (φ ψ : Formula X)
  | until (a b : ℝ≥0) (φ ψ : Formula X)
  | finOpen (c : ℝ≥0) (φ : Formula X)
  | globOpen (c : ℝ≥0) (φ : Formula X)

/-- `ξ ⊨ₜ φ`, [1, Sec. 2.2]. -/
def STL.Formula.Satisfies : STL.Formula X → (ℝ≥0 → X) → Prop
  | .atom p, ξ => p (ξ 0)
  | .not φ, ξ => ¬ φ.Satisfies ξ
  | .or φ ψ, ξ => φ.Satisfies ξ ∨ ψ.Satisfies ξ
  | .until a b φ ψ, ξ =>
      ∃ t, a ≤ t ∧ t ≤ b ∧ ψ.Satisfies (Time.shift ξ t) ∧ ∀ t' < t, φ.Satisfies (Time.shift ξ t')
  | .finOpen c φ, ξ => ∃ t, 0 < t ∧ t < c ∧ φ.Satisfies (Time.shift ξ t)
  | .globOpen c φ, ξ => ∀ t, 0 < t → t < c → φ.Satisfies (Time.shift ξ t)

/-- A non-temporal formula, as an STL formula. -/
def STL.Formula.ofPform : Pform X → STL.Formula X
  | .atom p => .atom p
  | .not ϱ => .not (ofPform ϱ)
  | .or ϱ₁ ϱ₂ => .or (ofPform ϱ₁) (ofPform ϱ₂)

/-- `φ` holds of every trace of a set, `M ⊨ₜ φ`. -/
def STL.Formula.HoldsOn (φ : STL.Formula X) (M : Set (ℝ≥0 → X)) : Prop := ∀ ξ ∈ M, φ.Satisfies ξ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
