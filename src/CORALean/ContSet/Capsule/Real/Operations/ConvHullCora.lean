module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull

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
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `S_out = convHull_(C, S)` for two capsules; `none` is the MATLAB error. -/
noncomputable def Capsule.convHullCora (C S : Capsule n) : Option (Capsule n) :=
  -- representsa_(S,'emptySet',eps)
  let sEmpty := decide (S.r < 0)
  -- `return` with `S_out` never assigned
  if sEmpty then none
  -- capsule-capsule case
  else some (C.convHull S)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
