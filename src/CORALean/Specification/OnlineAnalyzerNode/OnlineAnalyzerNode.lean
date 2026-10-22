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
CORA's node is a handle object that its methods mutate; here it is a value and a method returns
the new one. `ap`, the atomic proposition of an `AP` node, is of a type `A` that the node leaves
open (`atomicProposition`, `AtomicProposition S n`, in the analyzer); only `observeSet` uses it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


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
structure OnlineAnalyzerNode (A : Type) where
  kind : OnlineAnalyzerNode.Kind
  signal : FourValuedSignal ℝ
  prop : List STLInterval
  dropPropagated : Bool
  idx : ℕ
  parents : List ℕ
  children : List ℕ
  interval : Option STLInterval
  ap : Option A
  tentative : Option (TentativeKleeneSignal ℝ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
