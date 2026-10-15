module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# An ellipsoid lies in the box `q ± √diag(Q)`

CORA's `interval(E)`, `q ± sqrt(diag(Q))`, is sound and coordinatewise tight: coordinate `i` of
`G u` is the dot product of row `i` of `G` with `u`, at most `‖Gᵢ‖₂ ‖u‖₂` by Cauchy–Schwarz, and
`‖Gᵢ‖₂² = (G Gᵀ)ᵢᵢ = Qᵢᵢ`.
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

/-- A point of the ellipsoid is within `√Qᵢᵢ` of the center in coordinate `i`. -/
theorem Ellipsoid.abs_sub_le_sqrt_diag (E : Ellipsoid n) {x : Vec ℝ n} (hx : x ∈ E.construct)
    (i : Fin n) : |x i - E.q i| ≤ Real.sqrt (E.Q i i) := by -- --- PROOF ---
  obtain ⟨u, hu, rfl⟩ := hx
  -- the squared row of `G` is the diagonal entry of `Q`
  have hrow : ∑ j, E.G i j ^ 2 = E.Q i i := by
    have h := congrFun (congrFun E.G_mul_transpose i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => sq _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => E.G i j) u
  have hu2 : ∑ j, u j ^ 2 ≤ 1 := by
    rw [← norm₂_sq]
    nlinarith [norm₂_nonneg u]
  have hval : (E.q + E.G *ᵥ u) i - E.q i = ∑ j, E.G i j * u j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hval]
  refine Real.abs_le_sqrt ?_
  calc (∑ j, E.G i j * u j) ^ 2 ≤ (∑ j, E.G i j ^ 2) * ∑ j, u j ^ 2 := hcs
    _ ≤ (∑ j, E.G i j ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hu2 (Finset.sum_nonneg fun j _ => sq_nonneg _)
    _ = E.Q i i := by rw [mul_one, hrow]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
