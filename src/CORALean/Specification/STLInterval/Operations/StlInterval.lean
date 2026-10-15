module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `stlInterval(lb,ub,lc,rc)`

The constructor of `@stlInterval/stlInterval.m` (`aux_computeProperties`): an infinite bound is
open, and `lb > ub`, or `lb = ub` with an open end, gives the empty interval `stlInterval()`.
`CHECKS_ENABLED`'s `lb < 0` error is the hypothesis `0 ≤ lb` (see `STLInterval`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.stlInterval (lb ub : EReal) (lc rc : Bool) (hlb : 0 ≤ lb) :
    STLInterval :=
  -- 1. an infinite bound is open
  let lc' := if lb = ⊥ ∨ lb = ⊤ then false else lc
  let rc' := if ub = ⊥ ∨ ub = ⊤ then false else rc
  -- 2. `lb > ub`, or `lb = ub` with an open end, is empty
  if h : lb < ub ∨ (lb = ub ∧ lc' = true ∧ rc' = true) then
    .nonempty lb ub lc' rc' (by grind) (by grind) h hlb
  else .empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
