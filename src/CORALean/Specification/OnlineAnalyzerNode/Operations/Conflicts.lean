module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol
public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Operations.Supremum

@[expose] public section

/-!
# New observations for already propagated times

The check at the start of `observeSet`: for every interval `prop(i)` propagated to a parent with
upper bound `pUb` and closedness `pRc`, an observation from `lb` (closed if `lc`) must not reach
back before it, `pUb > lb || (withinTol(pUb,lb,eps) && pRc && lc)`; otherwise CORA throws
`CORA:specialError`. Empty intervals are skipped; an empty observed interval has an empty `lb`,
which is a MATLAB error. `some true` is the former throw, `none` the latter.
Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
`OnlineAnalyzerNode.conflictsFloat`, deciding the same read as reals.

## Inputs
* `eps` – machine epsilon
* `lb` – lower bound of the observation
* `lc` – lower bound is closed

## Output
* whether an observation conflicts with a propagated interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether some propagated interval conflicts with an observation from `lb` on. -/
noncomputable def OnlineAnalyzerNode.conflicts (eps : ℝ) (lb : Option (WithTop ℝ)) (lc : Bool) :
    List (STLInterval ℝ) → Option Bool
  | [] => some false
  | p :: rest =>
    match p.supremum.value, lb with
    -- if ~isempty(pUb) && ...
    | none, _ => OnlineAnalyzerNode.conflicts eps lb lc rest
    | some _, none => none
    | some pUb, some lb' =>
      open Classical in
      if STLInterval.toEReal pUb > STLInterval.toEReal lb' ∨
          (STLInterval.IsWithinTol eps (STLInterval.toEReal pUb) (STLInterval.toEReal lb') ∧
            p.supremum.closed = true ∧ lc = true)
      then some true else OnlineAnalyzerNode.conflicts eps lb lc rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
