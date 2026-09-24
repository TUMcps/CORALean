import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# `Alg. 3`'s loop state

`VerifyIter`: what one iteration of [1, Alg. 3] computes before line 25 shrinks `ε_max`: the
four distances lines 6-17 aggregate, `ν̂_G`/`ν̌_G` over the safe sets and `ν̂_F`/`ν̌_F` over the
unsafe ones.

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


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 3] computes before line 25 shrinks `ε_max`: the four
distances lines 6-17 aggregate, `ν̂_G`/`ν̌_G` over the safe sets and `ν̂_F`/`ν̌_F` over the
unsafe ones. -/
structure LinearSys.VerifyIter where
  /-- `ν̂_G`, lines 6-8: the outer approximation's worst distance to leaving a safe set. -/
  νGout : ℝ
  /-- `ν̌_G`, lines 6, 9-10: the inner approximation's. -/
  νGin : ℝ
  /-- `ν̂_F`, lines 12-14: the outer approximation's worst distance to meeting an unsafe set. -/
  νFout : ℝ
  /-- `ν̌_F`, lines 12, 15-16: the inner approximation's. -/
  νFin : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
