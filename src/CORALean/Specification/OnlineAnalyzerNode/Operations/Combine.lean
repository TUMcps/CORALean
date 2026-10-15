module

public import CORALean.Specification.FourValuedSignal.Operations.And
public import CORALean.Specification.FourValuedSignal.Operations.Or
public import CORALean.Specification.FourValuedSignal.Operations.Until
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# The signal a node derives from its children

`sig = combine(obj,childNodes)` of `onlineAnalyzerNode.m` (a private method): the negation of the
child's signal, the conjunction or disjunction of the children's signals, or the until of the two
children over the node's interval. CORA throws (`notSupported`, a failed `assert`) for a leaf, a
wrong number of children, and where `toBoolSignal()` of the four-valued operations throws; all are
`none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = combine(obj,childNodes)`. -/
noncomputable def OnlineAnalyzerNode.combine (n : OnlineAnalyzerNode A)
    (childNodes : List (OnlineAnalyzerNode A)) : Option (FourValuedSignal ℝ) :=
  match n.kind with
  -- only non-leaf nodes support combine
  | .true | .false | .ap => none
  -- sig = ~childNodes(1).signal
  | .not => match childNodes with
    | [c] => some c.signal.not
    | _ => none
  -- sig = childNodes(1).signal.and_(childNodes.signal)
  | .and => if childNodes = [] then none
    else FourValuedSignal.and_ (fun k : Fin childNodes.length => (childNodes.get k).signal)
  -- sig = childNodes(1).signal.or_(childNodes.signal)
  | .or => if childNodes = [] then none
    else FourValuedSignal.or_ (fun k : Fin childNodes.length => (childNodes.get k).signal)
  -- sig = childNodes(1).signal.until(obj.interval,childNodes(2).signal)
  | .until => match childNodes, n.interval with
    | [c1, c2], some I => c1.signal.until I c2.signal
    | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
