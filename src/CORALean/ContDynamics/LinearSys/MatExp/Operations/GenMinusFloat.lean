module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `G^{(-)}_h`, eq. (23), in floats

`Real.MatExp.genMinus`, [1]'s `(e^{AΔt} - I_n)G_h`, one column per generator, held as the
magnitude of each entry rather than the entry: `[e^{AΔt}] - I` is an interval matrix, its
product with a generator an interval vector, and the only consumer, `Δε^h_k`, reads the
generators' Euclidean length. So each entry is `Σ_k max(|inf|,|sup|) · |G_{kl}|` of the entry's
interval `[e^{AΔt}]_{jk} - δ_{jk}`, rounded up (`abs_genMinus_le`). The error box of `H` is
not read: `Real.genMinus` has no error box either, and its rounding is not a generator.

## Inputs
* `eA` – float exponential enclosure
* `H` – float state zonotope

## Output
* magnitudes of the generator columns of the propagated difference

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The magnitudes of `(e^{AΔt} - I_n)G_h`, from `[e^{AΔt}]` and `H`'s generators. -/
def MatExp.genMinus (eA : Interval (Mat 𝕋 n n)) (H : Zonotope (Vec 𝕋 n)) : Fin H.h → Vec 𝕋 n :=
  fun l j => sumUp fun k =>
    let lo := if j = k then subDown (eA.inf j k) one else eA.inf j k   -- [e^{AΔt} - I]_{jk}
    let hi := if j = k then subUp (eA.sup j k) one else eA.sup j k
    mulUp (maximum (absolute lo) (absolute hi)) (absolute (H.G l k))   -- ≥ |((e^{AΔt} - I)G_l)_j|

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
