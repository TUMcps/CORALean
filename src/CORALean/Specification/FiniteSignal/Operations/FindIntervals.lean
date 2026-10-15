module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.FindIntervalsLoop

@[expose] public section

/-!
# The maximal intervals where a condition holds

`int = findIntervals(sig,cond)` of `findIntervals.m`: the disjoint closed intervals `[start,
stop]` of the maximal runs of cells whose value satisfies `cond` (CORA returns `interval` objects,
the empty array if there is none; here pairs of bounds and the empty list). The first interval
starts at `0` if the first value satisfies `cond`; `start` is unset before, and set by a rising
edge before it is first read.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `int = findIntervals(sig,cond)`. -/
def FiniteSignal.findIntervals {T V : Type} [Zero T] (s : FiniteSignal T V) (cond : V → Bool) :
    List (T × T) :=
  -- if cond(sig.value(1)) then start = 0
  FiniteSignal.findIntervalsLoop cond 0 s.pairs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
