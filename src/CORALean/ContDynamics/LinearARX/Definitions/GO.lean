import CORALean.ContDynamics.LinearARX.LinearARX

/-!
# The output parameters of a general output model of an ARX system

The `C` and `D` of CORA's `p_GO` from `linearARX/computeGO` [1], for the `nk` steps
`0, …, nk-1`: `C k` gives the output `y(k)` from the initial window and `D k i` from the input
`u(i)`. Not kept: the state parameters `A` and `B` of the window, the reference signals and the
`tvp` parametrization; `F` and `E` are `0` for an ARX model.

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure LinearARX.GO (dy du p nk : ℕ) where
  C : Fin nk → Mat ℝ dy (p * dy)
  D : Fin nk → Fin nk → Mat ℝ dy du

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
