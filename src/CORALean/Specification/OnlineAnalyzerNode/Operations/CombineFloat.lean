module

public import CORALean.Specification.FourValuedSignal.Operations.And
public import CORALean.Specification.FourValuedSignal.Operations.Or
public import CORALean.Specification.FourValuedSignal.Operations.UntilFloat
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# The signal a node derives from its children, over a float scalar

`combine` with time stamps in `𝕋`: the negation, conjunction and disjunction read the time stamps
exactly, and the until is `FourValuedSignal.untilFloat`, so a `True` or `False` of the result is
that of `combine` on the nodes read as reals (`combineFloat_sound`). A leaf, a wrong number of
children and a failed `toBoolSignal()` are `none`.

## Inputs
* `n` – node
* `childNodes` – the node's children

## Output
* the signal derived from the children, or none for a leaf
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = combine(obj,childNodes)`, with the until of `untilFloat`. -/
def OnlineAnalyzerNode.combineFloat (n : OnlineAnalyzerNode 𝕋 A)
    (childNodes : List (OnlineAnalyzerNode 𝕋 A)) : Option (FourValuedSignal 𝕋) :=
  match n.kind with
  -- only non-leaf nodes support combine
  | .true | .false | .ap => none
  -- sig = ~childNodes(1).signal
  | .not => match childNodes with
    | [c] => some c.signal.not
    | _ => none
  -- sig = childNodes(1).signal.and_(childNodes.signal)
  | .and => if childNodes.isEmpty then none
    else FourValuedSignal.and_ (fun k : Fin childNodes.length => (childNodes.get k).signal)
  -- sig = childNodes(1).signal.or_(childNodes.signal)
  | .or => if childNodes.isEmpty then none
    else FourValuedSignal.or_ (fun k : Fin childNodes.length => (childNodes.get k).signal)
  -- sig = childNodes(1).signal.until(obj.interval,childNodes(2).signal)
  | .until => match childNodes, n.interval with
    | [c1, c2], some I => c1.signal.untilFloat I c2.signal
    | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
