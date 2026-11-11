module

public import CORALean.ContSet.ConZonotope.Float.Operations.FourierMotzkinBounds

@[expose] public section

/-!
# `ConZonotope.fourierMotzkinIter` over a floating-point scalar

[1, Prop. 3] applied `k` times from the unit box `B_q = [-1, 1]^q`, as CORA's
`aux_fourierMotzkinApproximation` in `conZonotope/approximateBoundsWithGPU` loops
(`options.nn.polytope_bound_approx_max_iter`).
CORA also stops early when no bound moves by more than `1e-8`; a pass that moves nothing changes
nothing, so the bounds after `k` passes are those after the early stop or tighter.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `k` – number of passes

## Output
* bounds of `⟨C, d⟩_H ∩ B_q` after `k` passes of [1, Prop. 3]

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". Proceedings of the International Conference on Learning
      Representations, 2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       04-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `k` passes of [1, Prop. 3] from the unit box. -/
def ConZonotope.fourierMotzkinIter (C : Mat 𝕋 p q) (d : Vec 𝕋 p) (k : ℕ) :
    Interval (Vec 𝕋 q) :=
  (ConZonotope.fourierMotzkinBounds C d)^[k] ⟨fun _ => neg one, fun _ => one⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
