module

public import CORALean.ContDynamics.LinearARX.LinearARX
public import CORALean.ContDynamics.NonlinearARX.NonlinearARX

@[expose] public section

/-!
# The regressor of `LinearARX.identify`

One data point of `aux_getDataPoints` in `priv_identifyDMD` [1]: the column
`[x(j-1); …; x(j-p); u(j); …; u(j-p)]` that `reshape(fliplr(...))` stacks, newest output first.
The two windows are `NonlinearARX.pastOut` and `NonlinearARX.pastIn`, which stack the same way.

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regressor column of the data point at step `k`, outputs `y` and inputs `u`. -/
def LinearARX.identifyRegressor (p : ℕ) (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du) (k : ℕ) :
    Vec ℝ (p * dy + (p + 1) * du) :=
  Fin.append (NonlinearARX.pastOut p y k) (NonlinearARX.pastIn p u k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
