module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.plusCellCora`: `plus(E, {S₁, …})` as CORA's code runs

`@ellipsoid/plus.m`, the branch for a cell array `S` (the last `if`, which the documentation
`S - contSet object (or cell array), numeric` promises and `inputArgsCheck` accepts):

```
if iscell(S) && all(cellfun(@(S_i) isa(S_i,'ellipsoid') || isa(S_i,'interval') ...
        || isa(S_i,'zonotope'),'UniformOutput',true))
    S = cellfun(@(S_i) ellipsoid(S_i),S,'UniformOutput',false);
    S_out = priv_plusEllipsoid([E;S],L,mode);
```

The first `cellfun` is given the function and the option name, no cell array: MATLAB stops with
`Input #2 expected to be a cell array, was char instead`. The earlier branches are all skipped for
a cell, and `reorderNumeric`, `equalDimCheck` and `inputArgsCheck` accept it. `none` is the MATLAB
error; the value of a call that does not error is not modelled. Read from the source, not run.

# CORA's `plus(E, {S₁, …})` always crashes

A sum of an ellipsoid with a cell array of ellipsoids, intervals or zonotopes is documented and
is accepted by `inputArgsCheck`, but `@ellipsoid/plus.m` raises an error for every cell, also the
empty one (the `cellfun` has no cell array argument). Read from the source, not run.

## Inputs
* `E` – ellipsoid
* `S` – list of ellipsoids

## Hypotheses
* none

## Conclusion
* the sum with a cell array errors for every input
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- Whether `plus(E, S)` for a cell array `S` of ellipsoids returns an ellipsoid (`some`) or
errors (`none`): it always errors. -/
def Ellipsoid.plusCellCora (_E : Ellipsoid n) (_S : List (Ellipsoid n)) : Option (Ellipsoid n) :=
  -- all(cellfun(@(S_i) ..., 'UniformOutput', true)): no cell array argument
  none

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plus(E, S)` errors for every ellipsoid and every cell array of ellipsoids. -/
theorem Ellipsoid.plus_cell_cora_crash (E : Ellipsoid n) (S : List (Ellipsoid n)) :
    E.plusCellCora S = none := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
