module

public import CORALean.Specification.STLInterval.Instances
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat

@[expose] public section

/-!
# New observations for already propagated times, over a float scalar

`conflicts` with time stamps in `𝕋`: the comparison `pUb > lb` and the test
`withinTol(pUb,lb,eps)` are decided exactly on the reals the bounds denote
(`withinTolFloat`), so the result is that of `conflicts` on the intervals read as reals
(`conflictsFloat_toReal`). `some true` is CORA's throw, `none` the MATLAB error of an empty
`lb`.

## Inputs
* `eps` – machine epsilon
* `lb` – lower bound of the observation
* `lc` – lower bound is closed

## Output
* whether an observation conflicts with a propagated interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether some propagated interval conflicts with an observation from `lb` on. -/
def OnlineAnalyzerNode.conflictsFloat (eps : 𝕋) (lb : Option (WithTop 𝕋)) (lc : Bool) :
    List (STLInterval 𝕋) → Option Bool
  | [] => some false
  | p :: rest =>
    match p.supremum.value, lb with
    -- if ~isempty(pUb) && ...
    | none, _ => OnlineAnalyzerNode.conflictsFloat eps lb lc rest
    | some _, none => none
    | some pUb, some lb' =>
      if STLInterval.toEReal pUb > STLInterval.toEReal lb' ∨
          (STLInterval.withinTolFloat eps pUb lb' = true ∧ p.supremum.closed = true ∧ lc = true)
      then some true else OnlineAnalyzerNode.conflictsFloat eps lb lc rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
