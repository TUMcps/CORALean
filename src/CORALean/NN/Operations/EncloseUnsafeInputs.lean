module

public import CORALean.NN.Operations.UnsafeInputConstraints
public import CORALean.ContSet.ConZonotope.Real.Operations.Constrain

@[expose] public section

/-!
# `SetBasedNet.encloseUnsafeInputs`

[1, Prop. 2]'s refined input set: `X` constrained to `X|_{C≤d}` (`Zonotope.constrain`) by the
constraints `C := A G_y(·,[q₀])` and `d := b - A c_y + |A G_y(·,[q_κ]\[q₀])| 1` that transfer the
unsafe set `U = ⟨A, b⟩_H` to the input's factors (`SetBasedNet.unsafeInputConstraints`).

## Inputs
* `N` – set-based network
* `X` – input zonotope
* `A` – unsafe-set matrix
* `b` – unsafe-set offset

## Output
* the constrained input set `X|_{C≤d}`

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X|_{C≤d}` for the constraints of [1, Prop. 2]. -/
noncomputable def SetBasedNet.encloseUnsafeInputs (N : SetBasedNet n k) (X : Zonotope (Vec ℝ n))
    (A : Mat ℝ p k) (b : Vec ℝ p) : ConZonotope (Vec ℝ n) :=
  X.constrain (N.unsafeInputConstraints X A b).1 (N.unsafeInputConstraints X A b).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
