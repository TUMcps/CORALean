module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.CombineLoop
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The pointwise combination of two signals

`sig = combine(op,varargin)` of `combine.m`: the binary operator applied piecewise to two signals,
trimmed to the shorter one and in normal form. CORA throws unless exactly two signals are given,
and in the constructor if its checks fail; both are `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = combine(op,varargin)`. -/
def FiniteSignal.combine? {T V W : Type} [LinearOrder T] [Zero T] [DecidableEq W]
    (op : V → V → W) (sigs : List (FiniteSignal T V)) : Option (FiniteSignal T W) :=
  match sigs with
  | [lhs, rhs] =>
    -- the loop, then `sig = finiteSignal(tim,val)`
    let tv := FiniteSignal.combineLoop op lhs.pairs rhs.pairs
    FiniteSignal.mk? (tv.map Prod.fst) (tv.map Prod.snd)
  -- the function only supports two input signals
  | _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
