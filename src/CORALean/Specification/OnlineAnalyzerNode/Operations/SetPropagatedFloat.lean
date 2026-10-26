module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllPropFloat
public import CORALean.Specification.STLInterval.Operations.ContainsFloat
public import CORALean.Specification.STLInterval.Operations.IsequalFloat

@[expose] public section

/-!
# Recording what is propagated to a parent, over a float scalar

`setPropagated` with time stamps in `𝕋`: the tests `isequal` and `contains_` are decided exactly
on the reals the bounds denote (`isequalFloat`, `containsFloat`) and the dropped interval is
`getAllPropFloat`, so the node read as reals is `setPropagated` of the node read as reals
(`setPropagatedFloat_toRealNode`); `none` where CORA throws.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `parent` – parent index
* `int` – propagated interval

## Output
* the node with the interval recorded, or none where CORA throws
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

/-- `setPropagated(obj,parent,int)`. -/
def OnlineAnalyzerNode.setPropagatedFloat (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 A)
    (parent : ℕ) (int : STLInterval 𝕋) : Option (OnlineAnalyzerNode 𝕋 A) :=
  -- i = obj.parents == parent
  let i := n.parents.idxOf parent
  match n.prop[i]? with
  | none => none
  | some old =>
    -- the new propagated is not allowed to be smaller than the old one
    if !STLInterval.isequalFloat eps old int && STLInterval.containsFloat eps old int then none
    else
      -- obj.prop(i) = int
      let m := { n with prop := n.prop.set i int }
      -- if obj.dropPropagated, obj.signal = obj.signal.set(obj.getAllProp(),Inconclusive)
      if m.dropPropagated then
        some { m with signal := m.signal.set (OnlineAnalyzerNode.getAllPropFloat eps m) .ii }
      else some m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
