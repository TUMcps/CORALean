module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropBound
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# The time up to which everything is propagated

`allProp = getAllProp(obj)` of `onlineAnalyzerNode.m` (a private method): the interval from `0` to
the smallest upper bound of the intervals propagated to the parents, closed at its end if that
bound's interval is; an empty entry (nothing propagated to that parent) gives `[0,0)`, and no
parent at all `[0,∞)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `allProp = getAllProp(obj)`. -/
noncomputable def OnlineAnalyzerNode.getAllProp (eps : ℝ) (n : OnlineAnalyzerNode A) :
    STLInterval :=
  -- ub = inf; rc = true; the loop; allProp = stlInterval(0,ub,true,rc)
  let b := OnlineAnalyzerNode.propBound eps n.prop (⊤, true)
  STLInterval.stlInterval 0 b.1 true b.2 le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
