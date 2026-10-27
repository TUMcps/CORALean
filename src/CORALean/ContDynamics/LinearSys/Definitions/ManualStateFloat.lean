module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Alg. 1`'s loop state, in floats

`ManualStateFloat`: what one iteration of [1, Alg. 1] hands the next when it runs in `𝕋`.
`t_k` is kept exactly in ℚ, the sum of the steps read back through `ToRat`, and as a float
bracket `tEnc` for the enclosures of `e^{A t_k}`. `P^u(t_k)`, a point in [1], is a
box here, the float enclosure of a point.

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next, in `𝕋`. -/
structure LinearSys.ManualStateFloat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  /-- `t_k`, line 5, relative to `tStart`. -/
  t : ℚ
  /-- A bracket of floats around `t_k`. -/
  tEnc : Interval 𝕋
  /-- `H(t_k)`, lines 2 and 7. -/
  H : Zonotope (Vec 𝕋 n)
  /-- `P^u(t_k)`, lines 2 and 6. -/
  Pu : Interval (Vec 𝕋 n)
  /-- `P̂^U(t_k)`, lines 2 and 10. -/
  PU : Zonotope (Vec 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
