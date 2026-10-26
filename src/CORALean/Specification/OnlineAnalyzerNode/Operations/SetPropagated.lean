module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllProp
public import CORALean.Specification.STLInterval.Definitions.Contains
public import CORALean.Specification.STLInterval.Definitions.Isequal

@[expose] public section

/-!
# Recording what is propagated to a parent

`setPropagated(obj,parent,int)` of `onlineAnalyzerNode.m`: `int` is now propagated to the parent
with this index and, if `dropPropagated`, the signal is made inconclusive on everything propagated
to all parents. CORA throws if the new interval is smaller than the old or `parent` is no parent;
here `none`. `eps` is MATLAB's machine epsilon, the tolerance of the comparisons; the parents are
assumed distinct.
Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
`OnlineAnalyzerNode.setPropagatedFloat`, the same node read as reals.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `parent` – parent index
* `int` – propagated interval

## Output
* the node with the interval recorded, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `setPropagated(obj,parent,int)`. -/
noncomputable def OnlineAnalyzerNode.setPropagated (eps : ℝ) (n : OnlineAnalyzerNode ℝ A)
    (parent : ℕ) (int : STLInterval ℝ) : Option (OnlineAnalyzerNode ℝ A) :=
  open Classical in
  -- i = obj.parents == parent
  let i := n.parents.idxOf parent
  match n.prop[i]? with
  | none => none
  | some old =>
    -- the new propagated is not allowed to be smaller than the old one
    if ¬ STLInterval.isequal eps old int ∧ STLInterval.contains_ eps old int then none
    else
      -- obj.prop(i) = int
      let m := { n with prop := n.prop.set i int }
      -- if obj.dropPropagated, obj.signal = obj.signal.set(obj.getAllProp(),Inconclusive)
      if m.dropPropagated then
        some { m with signal := m.signal.set (OnlineAnalyzerNode.getAllProp eps m) .ii }
      else some m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
