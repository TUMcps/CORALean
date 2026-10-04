import CORALean.Specification.STL.Definitions.Shift
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Reach sequences and the traces they stand for

[1, Eq. 1]: `R : ℝ≥0 → Set X` is a reach sequence of a set of traces when every trace stays in
it, exact when `R t` is exactly the values taken at `t`; `traceSet R = C(R)` is every trace
that does. Hybrid automata are not modelled: `Traces(S)` is any set of traces.

[1, Eq. 2] and [1, Eq. 3]: `FinRep T R`, the breakpoints `T = {t₀, …, t_m}` with `R` constant
between two of them and, at a breakpoint, free: the alternating points and open intervals, as a
property of `R` rather than a list of sets. `CDivisible c T` is c-divisibility, `T ⊆ ℕc`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `C(R) = {ξ | ∀ t, ξ(t) ∈ R(t)}`. -/
def ReachSequence.traceSet (R : ℝ≥0 → Set X) : Set (ℝ≥0 → X) := {ξ | ∀ t, ξ t ∈ R t}

/-- [1, Eq. 1]: `{ξ(t) | ξ ∈ Traces} ⊆ R(t)` for all `t`. -/
def ReachSequence.Encloses (R : ℝ≥0 → Set X) (Traces : Set (ℝ≥0 → X)) : Prop :=
  ∀ t, ∀ ξ ∈ Traces, ξ t ∈ R t

/-- [1, Eq. 1] with `=`: `R(t)` is exactly the set of values at `t`. -/
def ReachSequence.IsExact (R : ℝ≥0 → Set X) (Traces : Set (ℝ≥0 → X)) : Prop :=
  ∀ t, R t = {x | ∃ ξ ∈ Traces, ξ t = x}

/-- [1, Eq. 2]: `R` is constant on every interval holding no breakpoint of `T`. -/
def ReachSequence.FinRep (T : Finset ℝ≥0) (R : ℝ≥0 → Set X) : Prop :=
  ∀ s t, (∀ u ∈ T, u ∉ Set.uIcc s t) → R s = R t

/-- [1, Lemma 2]: every breakpoint is a multiple `k·c` of `c`. -/
def ReachSequence.CDivisible (c : ℝ≥0) (T : Finset ℝ≥0) : Prop := ∀ u ∈ T, ∃ k : ℕ, u = k * c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
