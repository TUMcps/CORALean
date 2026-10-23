module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Signal temporal logic over discrete time

[1, Sec. II-B (semantics)]: formulas in negation normal form,
`φ ::= μ | ¬μ | φ ∧ ψ | φ ∨ ψ | □[a,b] ψ | φ U[a,b] ψ`, with `◇[a,b]` beside them, over a run
`x₀ x₁ …` of a discrete-time system; `μ` holds where `μ(xₜ) > 0`, `□[a,b] φ` at every step of
`[t+a, t+b]`, `φ U[a,b] ψ` where `ψ` holds at some `t'` there and `φ` on all of `[t, t']`. Each
interval carries `a ≤ b`. `STL.Formula` is continuous-time STL.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A discrete-time STL formula in negation normal form over predicates `μ : X → ℝ`. -/
inductive STL.DFormula (X : Type)
  | pred (μ : X → ℝ)
  | npred (μ : X → ℝ)
  | and (φ ψ : STL.DFormula X)
  | or (φ ψ : STL.DFormula X)
  | always (a b : ℕ) (hab : a ≤ b) (φ : STL.DFormula X)
  | eventually (a b : ℕ) (hab : a ≤ b) (φ : STL.DFormula X)
  | until (a b : ℕ) (hab : a ≤ b) (φ ψ : STL.DFormula X)

variable {X : Type}

/-- `(x, t) ⊨ φ`, [1, Sec. II-B (semantics)]. -/
def STL.DFormula.Sat : STL.DFormula X → (ℕ → X) → ℕ → Prop
  | .pred μ, x, t => 0 < μ (x t)
  | .npred μ, x, t => ¬ 0 < μ (x t)
  | .and φ ψ, x, t => φ.Sat x t ∧ ψ.Sat x t
  | .or φ ψ, x, t => φ.Sat x t ∨ ψ.Sat x t
  | .always a b _ φ, x, t => ∀ t' ∈ Finset.Icc (t + a) (t + b), φ.Sat x t'
  | .eventually a b _ φ, x, t => ∃ t' ∈ Finset.Icc (t + a) (t + b), φ.Sat x t'
  | .until a b _ φ ψ, x, t =>
      ∃ t' ∈ Finset.Icc (t + a) (t + b), ψ.Sat x t' ∧ ∀ t'' ∈ Finset.Icc t t', φ.Sat x t''

/-- `⊤`, the predicate `μ ≡ 1`. -/
abbrev STL.DFormula.tt : STL.DFormula X := .pred fun _ => 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
