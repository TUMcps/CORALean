import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Alg. 2`'s loop state

`AutoState`: what one iteration of [1, Alg. 2] hands the next.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 2] hands the next: lines 1-2's five sets and the time,
step and two accumulated errors lines 5, 29 and 33 carry across iterations. -/
structure LinearSys.AutoState (n : ℕ) where
  /-- `t_k`, line 4. -/
  t : ℝ
  /-- `Δt_{k-1}`, the step line 5 doubles. -/
  Δt : ℝ
  /-- `H(t_k)`, lines 1 and 26 — exact, never a hat. -/
  H : Zonotope (Vec ℝ n)
  /-- `P^u(t_k)`, lines 2 and 25 — a point, not a set. -/
  Pu : Vec ℝ n
  /-- `P̂^U_0(t_k)`, lines 2 and 18. -/
  PU0 : Zonotope (Vec ℝ n)
  /-- `P̂^U_∞(t_k)`, lines 2 and 17. -/
  PUinf : Zonotope (Vec ℝ n)
  /-- `ε^a_k`, lines 1 (as `0`) and 29, eq. (33). -/
  εa : ℝ
  /-- `ε^r_k`, lines 1 (as `0`) and 29, eq. (28). -/
  εr : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
