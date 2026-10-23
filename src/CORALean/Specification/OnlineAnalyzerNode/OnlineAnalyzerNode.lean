module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal

@[expose] public section

/-!
# Nodes of the online analyzer

CORA's `onlineAnalyzerNode` (`specification/onlineAnalyzerNode.m`): one node of the syntax tree of
an STL formula in the online analysis. A node has a `kind` (CORA's `type`: `true`, `false`, `AP`,
`~`, `|`, `&`, `until`), the four-valued `signal` known for its subformula, for each parent the
interval `prop` already propagated to it, and, for an atomic proposition, a `tentative` signal.
CORA's node is a handle object that its methods mutate; here a method returns the new one. `ap`, the
atomic proposition of an `AP` node, is of a type `A` that the node leaves open (`atomicProposition`,
`AtomicProposition S n`, in the analyzer); only `observeSet` uses it. Times are over a scalar `𝕋`. A
node's `signal` and the interval propagated to it are [1, Alg. 2]'s `n.signal` and `n.irr`.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The kinds of node of the syntax tree: true, false, atomic proposition, negation, disjunction,
conjunction and until. -/
inductive OnlineAnalyzerNode.Kind
  | true
  | false
  | ap
  | not
  | or
  | and
  | until
  deriving DecidableEq

/-- A node of the syntax tree of an STL formula in the online analysis: its kind, the four-valued
signal known for its subformula, its parents and children, interval and atomic proposition. -/
structure OnlineAnalyzerNode (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (A : Type) where
  kind : OnlineAnalyzerNode.Kind
  signal : FourValuedSignal 𝕋
  prop : List (STLInterval 𝕋)
  dropPropagated : Bool
  idx : ℕ
  parents : List ℕ
  children : List ℕ
  interval : Option (STLInterval 𝕋)
  ap : Option A
  tentative : Option (TentativeKleeneSignal 𝕋)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
