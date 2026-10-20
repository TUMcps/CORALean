module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.Indicator

@[expose] public section

/-!
# Marking where the property can be true

`setPossiblyTrue(obj,int)`: the indicator signal of the interval, true on it, is combined with the
signal `possiblyTrueSignal` by `|`, which is `finiteSignal.combine(@or,...)`. The interval `int`
is given by its bounds `lo` and `hi`, extended reals as `interval(lb,ub)` allows `inf`. CORA throws
for an empty or singleton interval (in `indicator`); here `none`.

## Inputs
* `obj` – signal builder
* `lo` – interval lower bound
* `hi` – interval upper bound

## Output
* builder with the property possibly true on the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `setPossiblyTrue(obj,int)`. -/
noncomputable def FiniteKleeneSignalBuilder.setPossiblyTrue? (obj : FiniteKleeneSignalBuilder)
    (lo hi : EReal) : Option FiniteKleeneSignalBuilder :=
  -- obtain duration of signal
  let dur := obj.possiblyTrueSignal.duration
  -- construct indicator signal for given interval
  (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
    -- combine signals
    (FiniteSignal.combine? (· || ·) [obj.possiblyTrueSignal, ind]).map fun sig =>
      { obj with possiblyTrueSignal := sig }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
