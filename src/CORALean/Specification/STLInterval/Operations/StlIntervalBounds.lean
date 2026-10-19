module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `stlInterval` with real bounds

`stlInterval(lb,ub,lc,rc)` for a real lower bound and an upper bound that is real or `inf`, the
bounds `findIntervals` and `conclusiveInterval` read off a signal. CORA rejects `lb < 0`; the
model returns `stlInterval()` for it, a case no valid signal reaches (its time points are `≥ 0`).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (bounds
over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `stlInterval(lb,ub,lc,rc)` for real bounds, `ub` possibly `inf`; a negative `lb`, which CORA
rejects, gives `stlInterval()`. -/
noncomputable def STLInterval.stlIntervalBounds (lb : ℝ) (ub : WithTop ℝ) (lc rc : Bool) :
    STLInterval :=
  if hlb : 0 ≤ lb then
    STLInterval.stlInterval (lb : EReal) (ub.recTopCoe (⊤ : EReal) (fun r => (r : EReal))) lc rc
      (EReal.coe_nonneg.2 hlb)
  else .empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
