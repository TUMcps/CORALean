module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `Ellipsoid.convHullCora`: `convHull_` as CORA's code runs, an empty second operand included

`@ellipsoid/convHull_.m` opens the case of an empty second operand with

```
% convex hull with empty set
if representsa_(S,'emptySet',eps)
    return;
end
```

(l. 56-58) and never assigns `S_out` before that `return`: MATLAB stops with `Output argument
'S_out' (and maybe others) not assigned during call`. The result for two ellipsoids is
`or(E,S,'outer')`, an SDP-solver result, taken here as a parameter `orOuter`. The model has no empty
ellipsoid, so `ellipsoid.empty(n)` is `none` in the second operand. Read from the source, not run.

# CORA's `ellipsoid/convHull_` errors on an empty second operand

The branch for an empty `S` (l. 56-58 of `@ellipsoid/convHull_.m`) executes `return` without
having set `S_out`, so `convHull(E, ellipsoid.empty(n))` raises MATLAB's "output argument not
assigned" error, where the hull of a convex set with `∅` is the set itself. Read from the
source, not run.

## Inputs
* `orOuter` – outer hull of two ellipsoids
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* CORA returns no value for an empty second operand though the hull is `E`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `S_out = convHull_(E, S)` for ellipsoids, `S = none` standing for
`ellipsoid.empty(n)`; `none` as a result is the MATLAB error. -/
def Ellipsoid.convHullCora (orOuter : Ellipsoid n → Ellipsoid n → Ellipsoid n)
    (E : Ellipsoid n) (S : Option (Ellipsoid n)) : Option (Ellipsoid n) :=
  match S with
  -- representsa_(S,'emptySet',eps): `return` with `S_out` never assigned
  | none => none
  -- isa(S,'ellipsoid'): S_out = or(E,S,'outer')
  | some S' => some (orOuter E S')

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With an empty second operand CORA's `convHull_` returns no value, for any `or`, while the
hull is `E`. -/
theorem Ellipsoid.convHull_empty_cora_crash
    (orOuter : Ellipsoid n → Ellipsoid n → Ellipsoid n) (E : Ellipsoid n) :
    E.convHullCora orOuter none = none ∧
      convexHull ℝ (E.construct ∪ ∅) = E.construct := by
  refine ⟨rfl, ?_⟩
  rw [Set.union_empty]
  exact (Ellipsoid.convex_construct E).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
