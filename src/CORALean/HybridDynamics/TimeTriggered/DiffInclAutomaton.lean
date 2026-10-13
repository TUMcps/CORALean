import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Hybrid automata with differential-inclusion flows, as [1] defines them

[1, Def. 1]'s tuple `(Modes, Var, Init, Flow, Trans, Inv)` over a normed space `X` of
continuous parts, flows `ẋ ∈ f_m(x)`, and their semantics: a continuous successor [1, Def. 4] is
a differentiable `g : [0, t] → X` with `g(δ) ∈ Inv(m)` and `ġ(δ) ∈ Flow(m)(g(δ))` on the open
interval, a discrete successor [1, Def. 5] takes a transition whose guard holds, and an execution
[1, Def. 6] is a finite chain of both from an initial state. `Exec d m x` says `(m, x)` ends an
execution of duration `d`; `reachLE T` is [1, Def. 7]'s `Reach≤T`.

This is not `HybridAutomaton`: the flow is any set-valued map, and a run carries its duration.
The invariant is read on the open interval only, as [1, Def. 4] prints it, and the discrete
successor is `(m', υ(x))`, [1, Def. 5] printing `(m, x')` for it.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {M X : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A transition `(m, G, υ, m')` of [1, Def. 1]: source, guard, reset and target. -/
structure DiffInclTransition (M X : Type) where
  source : M
  guard : Set X
  reset : X → X
  target : M

/-- `(Modes, Var, Init, Flow, Trans, Inv)` of [1, Def. 1], the flow a set of derivatives. -/
structure DiffInclAutomaton (M X : Type) where
  init : M → Set X
  flow : M → X → Set X
  inv : M → Set X
  trans : Set (DiffInclTransition M X)

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `(m, x')` is a continuous successor of `(m, x)` with dwell time `t`, [1, Def. 4]. -/
def DiffInclAutomaton.Flows (H : DiffInclAutomaton M X) (m : M) (x : X) (t : ℝ) (x' : X) :
    Prop :=
  0 < t ∧ ∃ g : ℝ → X, DifferentiableOn ℝ g (Set.Icc 0 t) ∧ g 0 = x ∧ g t = x' ∧
    ∀ δ ∈ Set.Ioo 0 t, g δ ∈ H.inv m ∧ deriv g δ ∈ H.flow m (g δ)

/-- `(m, x)` ends an execution of duration `d` ([1, Def. 6]): initial, flowed or jumped to. -/
inductive DiffInclAutomaton.Exec (H : DiffInclAutomaton M X) : ℝ → M → X → Prop where
  | init {m : M} {x : X} (hx : x ∈ H.init m) : H.Exec 0 m x
  | flow {d t : ℝ} {m : M} {x x' : X} (h : H.Exec d m x) (hf : H.Flows m x t x') :
      H.Exec (d + t) m x'
  | jump {d : ℝ} {m : M} {x : X} (h : H.Exec d m x) (e : DiffInclTransition M X)
      (he : e ∈ H.trans) (hm : e.source = m) (hx : x ∈ e.guard) :
      H.Exec d e.target (e.reset x)

/-- `Reach(H)`, the continuous parts of the end states of all executions, [1, Def. 7]. -/
def DiffInclAutomaton.reach (H : DiffInclAutomaton M X) : Set X :=
  {x | ∃ d m, H.Exec d m x}

/-- `Reach≤T(H)`: those of executions of duration at most `T`, [1, Def. 7]. -/
def DiffInclAutomaton.reachLE (H : DiffInclAutomaton M X) (T : ℝ) : Set X :=
  {x | ∃ d m, d ≤ T ∧ H.Exec d m x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
