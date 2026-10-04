import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Signal temporal logic over discrete time, and its robustness

[1, Sec. II-B (semantics)]: formulas in negation normal form,
`φ ::= μ | ¬μ | φ ∧ ψ | φ ∨ ψ | □[a,b] ψ | φ U[a,b] ψ`, with `◇[a,b]` beside them, over a run
`x₀ x₁ …` of a discrete-time system; `μ` holds where `μ(xₜ) > 0`, `□[a,b] φ` at every step of
`[t+a, t+b]`, `φ U[a,b] ψ` where `ψ` holds at some `t'` there and `φ` on all of `[t, t']`. Each
interval carries `a ≤ b`. [1, Sec. II-C]: the robustness `ρ`, by `min` and `max` along the same
recursion; the paper prints no `ρ` of `◇`, which is taken as the `max` dual to `□`.
`STL.Formula` is continuous-time STL.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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

/-- `ρ^φ(x, t)`, [1, Sec. II-C]. -/
noncomputable def STL.DFormula.rob : STL.DFormula X → (ℕ → X) → ℕ → ℝ
  | .pred μ, x, t => μ (x t)
  | .npred μ, x, t => -μ (x t)
  | .and φ ψ, x, t => min (φ.rob x t) (ψ.rob x t)
  | .or φ ψ, x, t => max (φ.rob x t) (ψ.rob x t)
  | .always a b hab φ, x, t =>
      (Finset.Icc (t + a) (t + b)).inf' (Finset.nonempty_Icc.mpr (by omega)) fun t' => φ.rob x t'
  | .eventually a b hab φ, x, t =>
      (Finset.Icc (t + a) (t + b)).sup' (Finset.nonempty_Icc.mpr (by omega)) fun t' => φ.rob x t'
  | .until a b hab φ ψ, x, t =>
      (Finset.Icc (t + a) (t + b)).attach.sup'
        (Finset.attach_nonempty_iff.mpr (Finset.nonempty_Icc.mpr (by omega))) fun t' =>
          min (ψ.rob x t'.1) ((Finset.Icc t t'.1).inf'
            (Finset.nonempty_Icc.mpr (by have := (Finset.mem_Icc.mp t'.2).1; omega))
            fun t'' => φ.rob x t'')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
