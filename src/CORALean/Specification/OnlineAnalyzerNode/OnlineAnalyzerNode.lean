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
the new one. `ap`, the atomic proposition of an `AP` node, is not stored: `atomicProposition` is
not formalized (its `canBeTrue` and `canBeFalse` only enter `observeSet`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive OnlineAnalyzerNode.Kind
  | true
  | false
  | ap
  | not
  | or
  | and
  | until
  deriving DecidableEq

structure OnlineAnalyzerNode where
  kind : OnlineAnalyzerNode.Kind
  signal : FourValuedSignal ℝ
  prop : List STLInterval
  dropPropagated : Bool
  idx : ℕ
  parents : List ℕ
  children : List ℕ
  interval : Option STLInterval
  tentative : Option (TentativeKleeneSignal ℝ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
