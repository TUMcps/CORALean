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

`propagate(obj,childNodes,makeValid)` of `onlineAnalyzerNode.m`: a `true` or `false` node has
nothing to do. An `AP` node makes the tentative observations on the interval `makeValid` final: it
merges them into its signal and removes them from the tentative signal. Any other node merges the
combination of its children's signals into its own, finds the interval up to which its signal is
conclusive given what is already propagated to its parents, and tells the children
(`setPropagated`). The nodes are values here: the result is the new node and the new children,
`none` where CORA throws.
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
noncomputable def OnlineAnalyzerNode.propagate (eps : ℝ) (n : OnlineAnalyzerNode A)
    (childNodes : List (OnlineAnalyzerNode A)) (makeValid : STLInterval) :
    Option ((OnlineAnalyzerNode A) × List (OnlineAnalyzerNode A)) :=
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
      (childNodes.mapM fun (c : OnlineAnalyzerNode A) => c.setPropagated eps m.idx concInt).map
        fun cs => (m, cs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
