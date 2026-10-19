module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Theorems.Convex
public import CORALean.ContSet.Capsule.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `Capsule.convHullCora`: `convHull_` as CORA's code runs, an empty second operand included

`@capsule/convHull_.m` answers the convex hull with an empty set by

```
% convex hull with empty set is the other set
if representsa_(S,'emptySet',eps)
    return;
end
```

(l. 57-59) but never assigns the output `S_out` before that `return`, so MATLAB stops with
`Output argument 'S_out' (and maybe others) not assigned during call`. The correct result, as
the comment says, is `C`. Read from the source, not run.

An empty capsule is modelled as `Capsule.empty`, radius `-1` (`isempty(S.r)` in CORA).

# CORA's `capsule/convHull_` errors on an empty second operand

The branch for an empty `S` (l. 57-59 of `@capsule/convHull_.m`) executes `return` without having
set `S_out`, so `convHull(C, capsule.empty(n))` raises MATLAB's "output argument not assigned"
error, where the hull of a convex set with `∅` is the set itself. Read from the source, not run.

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* CORA's `convHull_` with an empty operand yields no output, though the hull is `C`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `S_out = convHull_(C, S)` for two capsules; `none` is the MATLAB error. -/
noncomputable def Capsule.convHullCora (C S : Capsule n) : Option (Capsule n) :=
  -- representsa_(S,'emptySet',eps)
  let sEmpty := decide (S.r < 0)
  -- `return` with `S_out` never assigned
  if sEmpty then none
  -- capsule-capsule case
  else some (C.convHull S)

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `S = capsule.empty n` CORA's `convHull_` returns no value, while the hull is `C`. -/
theorem Capsule.convHull_empty_cora_crash (C : Capsule n) :
    C.convHullCora (Capsule.empty n) = none ∧
      convexHull ℝ (C.construct ∪ (Capsule.empty n).construct) = C.construct := by
  refine ⟨by simp [Capsule.convHullCora, Capsule.empty], ?_⟩
  rw [Capsule.empty_exact, Set.union_empty]
  exact (Capsule.convex_construct C).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
