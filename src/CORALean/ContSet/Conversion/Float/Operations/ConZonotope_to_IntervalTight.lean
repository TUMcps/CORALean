module

public import CORALean.ContSet.ConZonotope.Float.Operations.FourierMotzkinIter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# A constrained zonotope as a box that keeps the constraints, over a floating-point scalar

CORA's `conZonotope/interval` solves two linear programs per coordinate over `A β = b`,
`|β| ≤ 1`. No float program is reproducible bit for bit, so the coefficients are bounded by `k`
passes of `ConZonotope.fourierMotzkinIter` [1, Prop. 3] on the rows of the constraint (slacks folded
in, each equality as two halves), pure float arithmetic. The box is `c + G [β] + I_error`, with the
float zonotope image of the box of `β`. Outer for every `k`; at `k = 0` the zonotope's box, never
tighter than CORA's exact ranges.

## Inputs
* `k` – number of contraction passes
* `cZ` – float constrained zonotope

## Output
* box holding the set, constraints kept up to the passes

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". Proceedings of the International Conference on Learning
      Representations, 2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box of `c + G β + e` with `β` in the Fourier-Motzkin box of the constraint after `k` passes,
whose rows have the slacks folded in and no error box. -/
def ConZonotope.intervalTight (k : ℕ) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let P : HPolytope 𝕋 (Vec 𝕋 cZ.h) := { cZ.P with I_error := Interval.origin cZ.h }
  let Q := P.absorbRounding                                 -- inequality rows only
  let J := ConZonotope.fourierMotzkinIter Q.A Q.b k          -- the box of the coefficients
  let GJ := (Zonotope.mtimes (fun i j => cZ.G j i) J.zonotope).interval   -- the box of `G β`
  Interval.plus GJ ⟨fun i => addDown (cZ.c i) (cZ.I_error.inf i),   -- plus the center and the error
    fun i => addUp (cZ.c i) (cZ.I_error.sup i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
