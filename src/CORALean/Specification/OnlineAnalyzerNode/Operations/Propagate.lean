module

public import CORALean.Specification.FourValuedSignal.Operations.ConclusiveInterval
public import CORALean.Specification.FourValuedSignal.Operations.Merge
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Combine
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated
public import CORALean.Specification.TentativeKleeneSignal.Operations.GetInterval

@[expose] public section

/-!
# Propagating what is known to the parents

`propagate(obj,childNodes,makeValid)` of `onlineAnalyzerNode.m`: a `true` or `false` node does
nothing. An `AP` node makes its tentative observations on `makeValid` final. Any other node merges
the combination of its children's signals into its own, finds the interval up to which it is
conclusive given what its parents have, and tells the children (`setPropagated`). The result is
the new node and children, `none` where CORA throws.
Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
`OnlineAnalyzerNode.propagateFloat`.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `childNodes` – the node's children
* `makeValid` – interval to make final

## Output
* the propagated node with its children, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagate(obj,childNodes,makeValid)`. -/
noncomputable def OnlineAnalyzerNode.propagate (eps : ℝ) (n : OnlineAnalyzerNode ℝ A)
    (childNodes : List (OnlineAnalyzerNode ℝ A)) (makeValid : STLInterval ℝ) :
    Option ((OnlineAnalyzerNode ℝ A) × List (OnlineAnalyzerNode ℝ A)) :=
  match n.kind with
  | .true | .false => some (n, childNodes)
  | .ap =>
    match n.tentative, makeValid with
    -- if ~isemptyobject(makeValid)
    | some tent, .nonempty .. =>
      -- final = obj.tentative.getInterval(makeValid); obj.signal = obj.signal.merge(final)
      let final := tent.getInterval makeValid
      some ({ n with signal := n.signal.merge final,
                     tentative := some (tent.setInvalid makeValid) }, childNodes)
    | _, _ => some (n, childNodes)
  | _ =>
    -- delta = obj.combine(childNodes); obj.signal = obj.signal.merge(delta)
    (n.combine childNodes).bind fun delta =>
      let m := { n with signal := n.signal.merge delta }
      -- concInt = conclusiveInterval(obj.signal,obj.getAllProp())
      let concInt := m.signal.conclusiveInterval (m.getAllProp eps)
      -- for i = 1:length(childNodes), childNodes(i).setPropagated(obj.idx,concInt)
      (childNodes.mapM fun (c : OnlineAnalyzerNode ℝ A) => c.setPropagated eps m.idx concInt).map
        fun cs => (m, cs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
