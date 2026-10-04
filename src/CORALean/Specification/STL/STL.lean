import CORALean.Specification.STL.Definitions.Pform
import CORALean.Specification.STL.Definitions.Shift

/-!
# Signal temporal logic

[1, Sec. 2.2]: `φ := p | ¬φ | φ₁ ∨ φ₂ | φ₁ U[a,b] φ₂` over traces `ξ : ℝ≥0 → X`, and
`ξ ⊨ₜ φ` by the printed recursion. `finOpen` and `globOpen` are the operators `F(0,c)` and
`G(0,c)` of [1, Sec. 4.1], which the paper writes over an open interval, with the semantics
`∃t ∈ (0,c)` and `∀t ∈ (0,c)` the closed-interval `U` cannot express.

A formula is a Lean value over `X`, not over a name set `AP`: see `Pform`. The derived
operators are definitions, `release` the dual of `until` that [1, Lemma 4] uses.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive STL.Formula (X : Type)
  | atom (p : X → Prop)
  | not (φ : Formula X)
  | or (φ ψ : Formula X)
  | until (a b : ℝ≥0) (φ ψ : Formula X)
  | finOpen (c : ℝ≥0) (φ : Formula X)
  | globOpen (c : ℝ≥0) (φ : Formula X)

/-- `ξ ⊨ₜ φ`, [1, Sec. 2.2]. -/
def STL.Formula.Sat : STL.Formula X → (ℝ≥0 → X) → Prop
  | .atom p, ξ => p (ξ 0)
  | .not φ, ξ => ¬ φ.Sat ξ
  | .or φ ψ, ξ => φ.Sat ξ ∨ ψ.Sat ξ
  | .until a b φ ψ, ξ =>
      ∃ t, a ≤ t ∧ t ≤ b ∧ ψ.Sat (Time.shift ξ t) ∧ ∀ t' < t, φ.Sat (Time.shift ξ t')
  | .finOpen c φ, ξ => ∃ t, 0 < t ∧ t < c ∧ φ.Sat (Time.shift ξ t)
  | .globOpen c φ, ξ => ∀ t, 0 < t → t < c → φ.Sat (Time.shift ξ t)

/-- A non-temporal formula, as an STL formula. -/
def STL.Formula.ofPform : Pform X → STL.Formula X
  | .atom p => .atom p
  | .not ϱ => .not (ofPform ϱ)
  | .or ϱ₁ ϱ₂ => .or (ofPform ϱ₁) (ofPform ϱ₂)

/-- `true`. -/
def STL.Formula.tt : STL.Formula X := .atom fun _ => True

/-- `false`. -/
def STL.Formula.ff : STL.Formula X := .atom fun _ => False

/-- `φ ∧ ψ`, by De Morgan. -/
def STL.Formula.and (φ ψ : STL.Formula X) : STL.Formula X := .not (.or (.not φ) (.not ψ))

/-- The continuous next-operator `Xₐ φ := true U[a,a] φ`. -/
def STL.Formula.next (a : ℝ≥0) (φ : STL.Formula X) : STL.Formula X := .until a a .tt φ

/-- `F[a,b] φ := true U[a,b] φ`. -/
def STL.Formula.finally (a b : ℝ≥0) (φ : STL.Formula X) : STL.Formula X := .until a b .tt φ

/-- `φ R[a,b] ψ := ¬(¬φ U[a,b] ¬ψ)`. -/
def STL.Formula.release (a b : ℝ≥0) (φ ψ : STL.Formula X) : STL.Formula X :=
  .not (.until a b (.not φ) (.not ψ))

/-- `⋁` of a list, `false` for the empty one. -/
def STL.Formula.bigOr (l : List (STL.Formula X)) : STL.Formula X := l.foldr .or .ff

/-- `⋀` of a list, `true` for the empty one. -/
def STL.Formula.bigAnd (l : List (STL.Formula X)) : STL.Formula X := l.foldr .and .tt

/-- `φ` holds of every trace of a set, `M ⊨ₜ φ`. -/
def STL.Formula.HoldsOn (φ : STL.Formula X) (M : Set (ℝ≥0 → X)) : Prop := ∀ ξ ∈ M, φ.Sat ξ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
