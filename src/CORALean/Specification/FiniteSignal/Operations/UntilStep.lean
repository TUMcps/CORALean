module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Operations.UntilPiece

@[expose] public section

/-!
# One step of the until loop

The loop body of `until.m`: if `bint` is not empty and has positive volume, the signal is or-ed
with the indicator of `bint`. The or of `finiteSignal` is `combine` with the logical or.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop body for the runs `LR = (lint(i), rint(j))`. -/
noncomputable def FiniteSignal.untilStep (eps p : ℝ) (q : EReal) (dur : ℝ)
    (sig : FiniteSignal ℝ Bool) (LR : (ℝ × ℝ) × (ℝ × ℝ)) : Option (FiniteSignal ℝ Bool) :=
  match FiniteSignal.untilPiece eps p q LR.1 LR.2 with
  | none => some sig
  -- if ~representsa_(bint,'emptySet',eps) && volume(bint) > 0
  | some (lo, hi) =>
    if lo < hi then
      -- sig = sig | finiteSignal.indicator(dur,bint,up)
      (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
        FiniteSignal.combine? (fun x y => x || y) [sig, ind]
    else some sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
