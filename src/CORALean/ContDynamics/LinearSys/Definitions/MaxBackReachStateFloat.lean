module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# What one iteration of `Alg. 2` in floats hands the next

`MaxBackReachState` in `𝕋`, with three differences the guarantee forces. The time `t_k` is a
bracket, since a float need not hold it. `Z̲_U(t_k)` is *not* an inner set: its float
computation rounds both ways, so it is kept with a bound `UErr` on how far it lies outside the
exact set, and the guarantee of the inner approximation is made room for in the erosion of
`Ẑ_W(τ_k)`, not here. And `R̂^{∃∀}(-τ_{k-1})` is kept as the two summands line 12 adds,
`RH ⊕ -RU`: a float sum rounds the centre, which an inner approximation cannot absorb, while
the summands are each described by their stored numbers.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 2] hands the next, in floats. -/
structure LinearSys.MaxBackReachStateFloat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  /-- `t_k`, line 7: a lower end. -/
  tLo : 𝕋
  /-- `t_k`, line 7: an upper end. -/
  tHi : 𝕋
  /-- `Z̲_U(t_k)`, line 8: within `UErr` of the exact set, in every coordinate. -/
  ZU : Zonotope (Vec 𝕋 n)
  /-- How far `ZU` lies outside the exact `Z̲_U(t_k)`, per coordinate. -/
  UErr : Vec 𝕋 n
  /-- `Ẑ_{W₀}(t_k)`, line 9: an outer set. -/
  ZW₀ : Zonotope (Vec 𝕋 n)
  /-- `Ẑ_W(τ_{k-1})`, line 10: an outer set. -/
  ZW : Zonotope (Vec 𝕋 n)
  /-- The hull of line 11 mapped by `e^{-A t_k}`: the first summand of line 12. -/
  RH : ConZonotope 𝕋 (Vec 𝕋 n)
  /-- `e^{-A t_k}` applied to `Z̲_U(t_{k-1})`: line 12 subtracts it. -/
  RU : Zonotope (Vec 𝕋 n)

/-- `R̂^{∃∀}(-τ_{k-1})`, line 12: the first summand and the negated second. -/
def LinearSys.MaxBackReachStateFloat.R [SoundFloatArithmetic 𝕋]
    (s : LinearSys.MaxBackReachStateFloat 𝕋 n) : Set (Vec ℝ n) :=
  s.RH.construct + -s.RU.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
