module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.STLInterval.Instances
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat

@[expose] public section

/-!
# The time up to which everything is propagated, over a float scalar

`getAllProp` with time stamps in `𝕋`: the comparison `nUb < ub` and the test
`withinTol(nUb,ub,eps)` are decided exactly on the reals the bounds denote (`withinTolFloat`),
so the interval, read as reals, is `getAllProp` of the node read as reals
(`getAllPropFloat_toRealInterval`).

## Inputs
* `eps` – machine epsilon
* `n` – node

## Output
* the interval up to which everything is propagated
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop of `getAllProp`: the bound `ub` and its closedness `rc` after the intervals. -/
def OnlineAnalyzerNode.aux_propBoundFloat (eps : 𝕋) :
    List (STLInterval 𝕋) → WithTop 𝕋 × Bool → WithTop 𝕋 × Bool
  | [], st => st
  -- isemptyobject(obj.prop(i)): ub = 0; rc = false; break
  | .empty :: _, _ => ((0 : 𝕋), false)
  | .nonempty _ u _ nRc _ _ _ :: rest, (ub, rc) =>
    -- if nUb < ub || withinTol(nUb,ub,eps) && ~nRc
    if STLInterval.toEReal u < STLInterval.toEReal ub ∨
        (STLInterval.withinTolFloat eps u ub = true ∧ nRc = false) then
      OnlineAnalyzerNode.aux_propBoundFloat eps rest (u, nRc)
    else OnlineAnalyzerNode.aux_propBoundFloat eps rest (ub, rc)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `allProp = getAllProp(obj)`. -/
def OnlineAnalyzerNode.getAllPropFloat (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 A) : STLInterval 𝕋 :=
  -- ub = inf; rc = true; the loop; allProp = stlInterval(0,ub,true,rc)
  let b := OnlineAnalyzerNode.aux_propBoundFloat eps n.prop (⊤, true)
  STLInterval.stlInterval (0 : 𝕋) b.1 true b.2 toReal_zero_eq.ge

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
