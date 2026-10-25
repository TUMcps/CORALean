module

public import CORALean.ContSet.HPolytope.Real.Operations.SimplexRows
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `HPolytope.generateRandomH`

[1, Alg. 3]: the rows of `HPolytope.simplexRows`, all with offset `1`, mapped by
`x ↦ M x + z` (line 7). The image is written in halfspaces, `⟨A M⁻¹, 1 + A M⁻¹ z⟩`, which is the
image when `M` is invertible — what line 6 samples, and what `generateRandomH_isBounded` asks.

## Inputs
* `ℓ` – vectors indexed by `Fin m`
* `M` – `n × n` matrix
* `z` – point of length `n`

## Output
* the simplex rows `A` with offset `1`, mapped by `x ↦ M x + z`: `⟨A M⁻¹, 1 + A M⁻¹ z⟩`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.generateRandomH (ℓ : Fin m → Vec ℝ n) (M : Mat ℝ n n) (z : Vec ℝ n) :
    HPolytope (Vec ℝ n) :=
  -- lines 1-5
  let A : Mat ℝ (n + 1 + m) n := HPolytope.simplexRows ℓ
  -- line 7: `M ⟨A, 1⟩ + z`
  HPolytope.ineqs (A * M⁻¹) (1 + (A * M⁻¹) *ᵥ z)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
