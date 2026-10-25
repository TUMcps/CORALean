module

public import CORALean.ContSet.Zonotope.Real.Definitions.ColsSnoc
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# A determinant with a unit vector normal to the other columns

For a unit vector `v` normal to the columns `B`, `det [B x] = det [B v] · vᵀx`: the step `det [B_i
σλ] = σ det [B_i v_i] (v_iᵀλ)` of the derivation in [1, Sec. 6.1], which the paper takes from `Φ_i
= [B_i v_i]`. Here `x = (vᵀx) v + u` with `u` normal to `v`; the determinant is linear in the last
column; and `[B u]` has `v` as a left null vector, so its determinant is zero.

## Inputs
* `v` – unit vector
* `x` – appended column
* `B` – list of columns

## Hypotheses
* `hv` – `v` has unit norm
* `hB` – columns orthogonal to `v`

## Conclusion
* the determinant scales by the dot product with `v`

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem det_colsSnoc_eq_mul_dotProduct (v x : Vec ℝ (m + 1)) (B : Fin m → Vec ℝ (m + 1))
    (hv : v ⬝ᵥ v = 1) (hB : ∀ k, v ⬝ᵥ B k = 0) : -- --- CONCL ---
    (colsSnoc B x).det = (colsSnoc B v).det * (v ⬝ᵥ x) := by -- --- PROOF ---
  -- the matrix with last column `y` is the one with last column `v`, updated
  have hupd : ∀ y, colsSnoc B y = (colsSnoc B v).updateCol (Fin.last m) y := by
    intro y; ext i k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [colsSnoc]
    · simp [colsSnoc, (Fin.castSucc_lt_last k).ne]
  obtain ⟨s, hs⟩ : ∃ s, s = v ⬝ᵥ x := ⟨_, rfl⟩
  rw [← hs]
  -- split `x` into its part along `v` and the rest `u`, normal to `v`
  set u : Vec ℝ (m + 1) := x - s • v with hu
  have hxu : x = s • v + u := by simp [hu]
  have hvu : v ⬝ᵥ u = 0 := by simp [hu, dotProduct_sub, dotProduct_smul, hv, hs]
  -- all columns of `[B  u]` are normal to `v`, so it is singular
  have hz : (colsSnoc B u).det = 0 := by
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨v, ?_, ?_⟩
    · intro h0
      have := congrArg (fun w => w ⬝ᵥ w) h0
      simp only [dotProduct_zero, hv] at this
      exact one_ne_zero this
    · ext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simpa [Matrix.vecMul, dotProduct, colsSnoc] using hvu
      · simpa [Matrix.vecMul, dotProduct, colsSnoc] using hB k
  rw [hupd x, hxu, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ← hupd u, hz, ← hupd v]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
