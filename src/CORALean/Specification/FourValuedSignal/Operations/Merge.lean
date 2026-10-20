module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.FindIntervals

@[expose] public section

/-!
# Merging two four-valued signals

`sig = merge(obj,other)` of `fourValuedSignal.m`: `obj`, with the intervals where `other` is `True`,
`False` and `Unknown` set to those values in turn; where `other` is inconclusive `obj` stays.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## Inputs
* `obj` – four-valued signal
* `other` – signal whose known values override

## Output
* the merged four-valued signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = merge(obj,other)`. -/
noncomputable def FourValuedSignal.merge (obj other : FourValuedSignal ℝ) : FourValuedSignal ℝ :=
  -- 1. sig = obj
  let sig := obj
  -- 2. the intervals where `other` is True, False and Unknown are set in turn
  let trueInt := other.findIntervals FourValued.tt
  let sig := trueInt.foldl (fun sig I => sig.set I FourValued.tt) sig
  let falseInt := other.findIntervals FourValued.ff
  let sig := falseInt.foldl (fun sig I => sig.set I FourValued.ff) sig
  let unknownInt := other.findIntervals FourValued.uu
  unknownInt.foldl (fun sig I => sig.set I FourValued.uu) sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
