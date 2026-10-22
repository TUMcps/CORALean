module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# What one verification iteration computes, in floats

[1, Alg. 3]'s four aggregated distances, lines 6-17, as stored `𝕋` values: `ν̂_G`/`ν̌_G` over the
safe sets and `ν̂_F`/`ν̌_F` over the unsafe ones, and the accuracy `ε_max` that line 25 hands the
next iteration.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The values one iteration of the verification algorithm produces, as floats: the worst distances
of the outer and inner approximation to the safe and the unsafe sets, and the next accuracy. -/
structure LinearSys.VerifyIterFloat (𝕋 : Type) where
  /-- `ν̂_G`, lines 6-8: the outer approximation's worst distance to leaving a safe set. -/
  νGout : 𝕋
  /-- `ν̌_G`, lines 6, 9-10: the inner approximation's. -/
  νGin : 𝕋
  /-- `ν̂_F`, lines 12-14: the outer approximation's worst distance to meeting an unsafe set. -/
  νFout : 𝕋
  /-- `ν̌_F`, lines 12, 15-16: the inner approximation's. -/
  νFin : 𝕋
  /-- `ε_max`, line 25: the accuracy of the next iteration. -/
  εmax : 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
