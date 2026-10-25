module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Sign.Defs

@[expose] public section

/-!
# `Zonotope.zonotackFactors`

The factors of the falsification candidate of [1, Eq. 9], as CORA's `'zonotack'` falsification
in `neuralNetwork/verify` computes them: `β̃ = -sign(a G_y)` for a normal vector `a = A(i,·)` of
the unsafe set `A y ≤ b`, so that `ỹ = c_y + G_y β̃` is the vertex of `Y` that minimizes `a y`, the
one nearest the halfspace. [1, Eq. 9] prints `β̃ = sign(a G_y)`, the vertex maximizing `a y`, the
farthest from it; the sign is CORA's (`beta_ = -sign(...)`).

## Inputs
* `Y` – output zonotope
* `a` – normal vector of the unsafe set

## Output
* the factors `-sign(a G_y)` of the vertex minimizing `a y`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors `-sign(a G_y)` of the vertex of `Y` minimizing `a y`, [1, Eq. 9], CORA's sign. -/
noncomputable def Zonotope.zonotackFactors (Y : Zonotope (Vec ℝ k)) (a : Vec ℝ k) :
    Fin Y.h → ℝ :=
  fun j => -(SignType.sign (a ⬝ᵥ Y.G j) : ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
