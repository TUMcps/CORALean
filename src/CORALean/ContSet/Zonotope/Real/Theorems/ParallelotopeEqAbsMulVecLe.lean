module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# A parallelotope in halfspaces

`[1, Eq. 29]` writes the parallelotope `Π = ∑ᵢ [-1, 1] zᵢ` as `{x | V x ≤ 1}`,
`V` the rows `±zᵢ`; that is wrong (`parallelotope_eq_abs_mulVec_le_counterexample`): the
rows that cut out `∑ᵢ [-1, 1] wᵢ` are those of the inverse of the matrix `W` of the `wᵢ`.
So `{x | |zᵢᵀ x| ≤ 1}` is the parallelotope spanned by the columns of `Z⁻¹`, `Z` the matrix
with rows `zᵢ`, which is the reading the rest of the reduction needs: its polar is
`conv(±zᵢ)`. Centered anywhere.

## Inputs
* `Zm` – inverse matrix
* `W` – generator matrix
* `c` – center

## Hypotheses
* `hZW` – `Zm` is the inverse of `W`

## Conclusion
* the parallelotope is the set with bounded transformed coordinates

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.parallelotope_eq_abs_mulVec_le (Zm W : Mat ℝ n n) (hZW : Zm * W = 1)
    (c : Vec ℝ n) : -- --- CONCL ---
    (⟨n, c, fun j i => W i j⟩ : Zonotope (Vec ℝ n)).construct
      = {x | ∀ i, |(Zm *ᵥ (x - c)) i| ≤ 1} := by -- --- PROOF ---
  have hWZ : W * Zm = 1 := mul_eq_one_comm.mp hZW
  -- a point is `c + W β`
  have hgen : ∀ β : Fin n → ℝ, ∑ j, β j • (fun i => W i j) = W *ᵥ β := by
    intro β; ext i; simp [mulVec, dotProduct, mul_comm]
  ext x
  constructor
  · rintro ⟨β, hβ, rfl⟩ i
    rw [add_sub_cancel_left, hgen, mulVec_mulVec, hZW, one_mulVec]
    exact hβ i
  · intro hx
    refine ⟨Zm *ᵥ (x - c), hx, ?_⟩
    rw [hgen, mulVec_mulVec, hWZ, one_mulVec, add_sub_cancel]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
