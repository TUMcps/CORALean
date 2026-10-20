module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `PolyZonotope.eDiffTight`

The maximum itself: `max_{x ∈ [-1,1]} |x^a - x^b|`, [1, Prop. 3], which `eDiff` only bounds. CORA
reads it off numerically, `minMaxDiffPoly` evaluating `x^a - x^b` at the roots of its derivative and
at the ends of `[-1,1]`; here it is the closed form those roots lead to. Equal exponents: `0`.
Different parity: `2`, attained at `x = -1`. Equal parity: both powers are those of `|x|`, so the
drift is `|u^a - u^b|` on `u ∈ [0,1]`, largest at `u^c = l/h` for `l < h` the smaller and larger
exponent and `c = h - l`, where it is `(l/h)^(l/c) · (c/h)`, and `1` for `l = 0`. That is below
`eDiff`'s `1` for every `l > 0` (`eDiffTight_le_eDiff`), `0.385` at `(3, 1)` for instance.

## Inputs
* `a` – first exponent
* `b` – second exponent

## Output
* tight bound on the exponent difference

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest drift of two powers of a factor in `[-1,1]`: `0` for equal exponents, `2` for
exponents of different parity, `(l/h)^(l/(h-l)) · ((h-l)/h)` for equal parity and `l = min a b ≠ 0`,
`h = max a b`, and `1` for `l = 0`. -/
noncomputable def PolyZonotope.eDiffTight (a b : ℕ) : ℝ :=
  if a = b then 0
  else if a % 2 ≠ b % 2 then 2
  else
    let l := min a b
    let h := max a b
    if l = 0 then 1 else ((l : ℝ) / h) ^ ((l : ℝ) / ((h - l : ℕ) : ℝ)) * (((h - l : ℕ) : ℝ) / h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
