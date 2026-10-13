import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# What `nonlinParamSys/linearize` hands on

The linearization of the `paramInt` branch [1]: the point `(p.x, p.u)` it expands about, the
centre `p.p` of the parameter box, the zonotope `zf` of the constant term `f(p.x, p.u, p)`, and
the matrix zonotopes `zA`, `zB` of the Jacobians in the state and in the input, each over the
parameter box. CORA wraps them into a `linParamSys`, the input set `U = zB (U + uTrans - p.u)`
and the constant input `zf + Ucenter`; that packaging is not carried.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinParamSys.Linearized (n m q : ℕ) where
  xs : Vec ℝ n
  us : Vec ℝ m
  ps : Vec ℝ q
  zf : Zonotope (Vec ℝ n)
  zA : Zonotope (Mat ℝ n n)
  zB : Zonotope (Mat ℝ n m)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
