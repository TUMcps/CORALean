module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# The output parameters of a general output model of an ARX system

The `C` and `D` of CORA's `p_GO` from `linearARX/computeGO` [1], for the `nk` steps
`0, …, nk-1`: `C k` gives the output `y(k)` from the initial window and `D k i` from the input
`u(i)`. Not kept: the state parameters `A` and `B` of the window, the reference signals and the
`tvp` parametrization; `F` and `E` are `0` for an ARX model.

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The output parameters of a general output model of a linear ARX system: one `C` per output and
one `D` per input and output pair, for `nk` inputs. -/
structure LinearARX.GO (dy du p nk : ℕ) where
  C : Fin nk → Mat ℝ dy (p * dy)
  D : Fin nk → Fin nk → Mat ℝ dy du

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
