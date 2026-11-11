module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# `ConZonotope.fourierMotzkinBounds` over a floating-point scalar

[1, Prop. 3] on the stored floats: bounds of the constrained hypercube `⟨C, d⟩_H ∩ B` without a
linear program. Row `i` bounds every coordinate `j` with `C(i,j) ≠ 0` from the rest of the row over
the *initial* box `B`, `C⁺` against the lower and `C⁻` against the upper ends: exactly what
`Interval.contractHalfspace` does for one halfspace, its sums rounded upward and its quotients
outward. The bounds are the intersection over all rows of these contractions of `B` (each row reads
`B`, not the box the previous row left, as in the real layer's `fourierMotzkinBounds`).
CORA: `aux_fourierMotzkinApproximation` in `conZonotope/approximateBoundsWithGPU`.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `B` – initial bounds

## Output
* the bounds of `⟨C, d⟩_H ∩ B`, every row read at the initial box

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

variable {𝕋 : Type} [FloatOps 𝕋] {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3]: the intersection of the row-wise contractions of the initial box `B`, the running
box stored after each row so that no read replays the rows before it. -/
def ConZonotope.fourierMotzkinBounds (C : Mat 𝕋 p q) (d : Vec 𝕋 p) (B : Interval (Vec 𝕋 q)) :
    Interval (Vec 𝕋 q) :=
  (List.finRange p).foldl
    (fun J i => (J.intersection (B.contractHalfspace (C i) (d i))).materialise) B.materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
