module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Alg. 2`'s loop state, in floats

`AutoStateFloat`: what one iteration of [1, Alg. 2] hands the next when it runs in `𝕋`. `t_k`
is kept exactly in ℚ, the sum of the steps read back through `ToRat`, and as a float bracket
`[tLo, tHi]` for the enclosures of `e^{A t_k}`; the two accumulated errors `ε^a_k` and `ε^r_k`
are exact ℚ too. `P^u(t_k)`, a point in [1], is a box here, the float enclosure of a point.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 2] hands the next, in `𝕋`. -/
structure LinearSys.AutoStateFloat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  /-- `t_k`, line 4, relative to `tStart`. -/
  t : ℚ
  /-- A float below `t_k`. -/
  tLo : 𝕋
  /-- A float above `t_k`. -/
  tHi : 𝕋
  /-- `Δt_{k-1}`, the step line 5 doubles. -/
  Δt : 𝕋
  /-- `H(t_k)`, lines 1 and 26. -/
  H : Zonotope (Vec 𝕋 n)
  /-- `P^u(t_k)`, lines 2 and 25. -/
  Pu : Interval (Vec 𝕋 n)
  /-- `P̂^U_0(t_k)`, lines 2 and 18. -/
  PU0 : Zonotope (Vec 𝕋 n)
  /-- `P̂^U_∞(t_k)`, lines 2 and 17. -/
  PUinf : Zonotope (Vec 𝕋 n)
  /-- `ε^a_k`, lines 1 (as `0`) and 29, eq. (33). -/
  εa : ℚ
  /-- `ε^r_k`, lines 1 (as `0`) and 29, eq. (28). -/
  εr : ℚ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
