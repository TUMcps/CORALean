module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `HPolytope.simplexRows`

[1, Alg. 3], lines 1-5: the rows of the simplex `xᵢ ≤ 1`, `-(1/√n) ∑ xᵢ ≤ 1` — every row a unit
vector, so the unit ball touches every facet — followed by one row per sampled direction `ℓⱼ`,
all with offset `1`. The directions are inputs; sampling them is outside the formalization.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.simplexRows (ℓ : Fin m → Vec ℝ n) : Mat ℝ (n + 1 + m) n :=
  -- line 1: `[Iₙ  -(1/√n) 1]ᵀ`
  let A₀ : Fin (n + 1) → Vec ℝ n := Fin.append (fun i => Pi.single i 1) ![fun _ => -(1 / √n)]
  -- lines 2-5: the sampled directions, appended
  Matrix.of (Fin.append A₀ ℓ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
