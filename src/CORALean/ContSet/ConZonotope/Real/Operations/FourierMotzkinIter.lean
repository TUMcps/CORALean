module

public import CORALean.ContSet.ConZonotope.Real.Operations.FourierMotzkinBounds
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# `ConZonotope.fourierMotzkinIter`

[1, Prop. 3] applied `k` times from the unit box `B_q = [-1, 1]^q`, as [1, App. D] allows and
[1, App. A] does (at most `4` passes), and as CORA's `aux_fourierMotzkinApproximation` in
`conZonotope/approximateBoundsWithGPU` loops (`options.nn.polytope_bound_approx_max_iter`). CORA
also stops early when no bound moves by more than `1e-8`; a pass that moves nothing changes
nothing, so the bounds after `k` passes are those after the early stop or tighter.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `k` – number of passes

## Output
* bounds of `⟨C, d⟩_H ∩ B_q` after `k` passes of [1, Prop. 3]

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `k` passes of [1, Prop. 3] from the unit box. -/
noncomputable def ConZonotope.fourierMotzkinIter (C : Mat ℝ p q) (d : Vec ℝ p) (k : ℕ) :
    Interval (Vec ℝ q) :=
  (ConZonotope.fourierMotzkinBounds C d)^[k] ⟨fun _ => -1, fun _ => 1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
