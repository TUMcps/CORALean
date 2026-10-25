module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `Alg. 1`'s loop state

`ManualState`: what one iteration of [1, Alg. 1] hands the next: `t_k`, `H(t_k)`, `P^u(t_k)`,
`P̂^U(t_k)`, lines 1-2.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
