import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Alg. 1`'s loop state

`ManualState`: what one iteration of [1, Alg. 1] hands the next: `t_k`, `H(t_k)`, `P^u(t_k)`,
`P̂^U(t_k)`, lines 1-2.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next: `t_k`, `H(t_k)`, `P^u(t_k)`,
`P̂^U(t_k)`, lines 1-2. -/
structure LinearSys.ManualState (n : ℕ) where
  /-- `t_k`, line 5. -/
  t : ℝ
  /-- `H(t_k)`, lines 2 and 7. -/
  H : Zonotope (Vec ℝ n)
  /-- `P^u(t_k)`, lines 2 and 6 — a point, not a set. -/
  Pu : Vec ℝ n
  /-- `P̂^U(t_k)`, lines 2 and 10. -/
  PU : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
