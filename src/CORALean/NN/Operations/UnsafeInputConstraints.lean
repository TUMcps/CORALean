module

public import CORALean.NN.Theorems.LeForwardH
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `SetBasedNet.unsafeInputConstraints`

The constraints of [1, Prop. 2], which transfer the unsafe set `U = ⟨A, b⟩_H` from the output space
to the factors of the input set: with `Y = ⟨c_y, G_y⟩_Z = enclose(Φ, X)`, `C := A G_y(·,[q₀])`, on
the input's own `q₀` factors, and `d := b - A c_y + |A G_y(·,[q_κ]\[q₀])| 1`, the approximation
errors' factors bounded by the unit box. `X|_{C≤d}` (`Zonotope.constrain`) encloses the unsafe
inputs; the columns `[q₀]` are the input's because the forward propagation keeps them first
(`SetBasedNet.le_forward_h`).

## Inputs
* `N` – set-based network
* `X` – input zonotope
* `A` – unsafe-set matrix
* `b` – unsafe-set offset

## Output
* the constraints `(C, d)` on the input's factors

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `C := A G_y(·,[q₀])` and `d := b - A c_y + |A G_y(·,[q_κ]\[q₀])| 1`, [1, Prop. 2]. -/
noncomputable def SetBasedNet.unsafeInputConstraints (N : SetBasedNet n k)
    (X : Zonotope (Vec ℝ n)) (A : Mat ℝ p k) (b : Vec ℝ p) : Mat ℝ p X.h × Vec ℝ p :=
  -- 1. the output enclosure `Y = enclose(Φ, X)`
  let Y := N.forward X
  -- 2. `C := A G_y(·,[q₀])`, the input's factors
  let C : Mat ℝ p X.h := fun i j => (A *ᵥ Y.G (Fin.castLE (N.le_forward_h X) j)) i
  -- 3. `d := b - A c_y + |A G_y(·,[q_κ]\[q₀])| 1`, the other factors bounded
  let d : Vec ℝ p := fun i => b i - (A *ᵥ Y.c) i +
    ∑ j ∈ Finset.univ.filter (fun j : Fin Y.h => X.h ≤ j.val), |(A *ᵥ Y.G j) i|
  (C, d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
