module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# `q + Q w` is a point of the ellipsoid when `wᵀ Q w ≤ 1`

The certificate a float membership test checks, as CORA's `contains_` solves `Q \ (p - q)`:
`Q w = G (G w)` with `‖G w‖₂² = wᵀ G G w = wᵀ Q w`, so `G w` is in the unit ball. No inverse, and
no full rank: any `w` with `Q w = p - q` and `wᵀ Q w ≤ 1` shows `p` in the set.

## Inputs
* `E` – ellipsoid
* `w` – vector

## Hypotheses
* `hw` – `wᵀ Q w ≤ 1`

## Conclusion
* `q + Q w` lies in `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `q + Q w` lies in the ellipsoid when `wᵀ Q w ≤ 1`. -/
theorem Ellipsoid.add_mulVec_mem_construct (E : Ellipsoid n) {w : Vec ℝ n}
    (hw : w ⬝ᵥ (E.Q *ᵥ w) ≤ 1) : -- --- CONCL ---
    E.q + E.Q *ᵥ w ∈ E.construct := by -- --- PROOF ---
  -- the ellipsoid as `q + G u`, `‖u‖₂ ≤ 1`
  simp only [Ellipsoid.construct_eq_sqrt] at *
  have hGG : E.G * E.G = E.Q := by
    have h := E.G_mul_transpose
    rwa [E.G_transpose] at h
  refine ⟨E.G *ᵥ w, ?_, by rw [mulVec_mulVec, hGG]⟩
  -- `‖G w‖₂² = wᵀ Q w`
  have hsq : ‖E.G *ᵥ w‖₂ ^ 2 = w ⬝ᵥ (E.Q *ᵥ w) := by
    rw [← dotProduct_self, dotProduct_mulVec, ← mulVec_transpose, E.G_transpose,
      mulVec_mulVec, hGG, dotProduct_comm]
  nlinarith [norm₂_nonneg (E.G *ᵥ w)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
