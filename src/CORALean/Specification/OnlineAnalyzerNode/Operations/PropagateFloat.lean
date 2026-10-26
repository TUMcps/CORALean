module

public import CORALean.Specification.FourValuedSignal.Operations.ConclusiveInterval
public import CORALean.Specification.FourValuedSignal.Operations.Merge
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineAnalyzerNode.Operations.CombineFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagatedFloat
public import CORALean.Specification.TentativeKleeneSignal.Operations.GetInterval

@[expose] public section

/-!
# Propagating what is known to the parents, over a float scalar

`propagate` with time stamps in `𝕋`: the children's signal is `combineFloat`, whose `True` and
`False` are exact ones, and everything else reads the time stamps exactly (`getAllPropFloat`,
`setPropagatedFloat`), so the result read as reals is what `propagate` does with that signal
(`propagateFloat_toRealNode`). `none` where CORA throws.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `childNodes` – the node's children
* `makeValid` – interval to make final

## Output
* the propagated node with its children, or none where CORA throws
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

/-- `propagate(obj,childNodes,makeValid)`. -/
def OnlineAnalyzerNode.propagateFloat (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 A)
    (childNodes : List (OnlineAnalyzerNode 𝕋 A)) (makeValid : STLInterval 𝕋) :
    Option ((OnlineAnalyzerNode 𝕋 A) × List (OnlineAnalyzerNode 𝕋 A)) :=
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
    (n.combineFloat childNodes).bind fun delta =>
      let m := { n with signal := n.signal.merge delta }
      -- concInt = conclusiveInterval(obj.signal,obj.getAllProp())
      let concInt := m.signal.conclusiveInterval (m.getAllPropFloat eps)
      -- for i = 1:length(childNodes), childNodes(i).setPropagated(obj.idx,concInt)
      (childNodes.mapM fun (c : OnlineAnalyzerNode 𝕋 A) =>
        c.setPropagatedFloat eps m.idx concInt).map fun cs => (m, cs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
