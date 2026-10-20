module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqOfFactor

@[expose] public section

/-!
# A larger shape matrix gives a larger ellipsoid

`Q₁ ⪯ Q₂` (that is, `Q₂ - Q₁` positive semi-definite) about one center puts the first ellipsoid in
the second: `[G₁ | D^(1/2)]`, `D = Q₂ - Q₁`, is a factor of `Q₂`, so the second is the image of the
unit ball under it (`construct_eq_of_factor`), and a point `q + G₁ u` is its value at `(u, 0)`.
This is what a rounded shape matrix inflated above the exact one is sound by.

## Inputs
* `E₁` – smaller ellipsoid
* `E₂` – larger ellipsoid

## Hypotheses
* `hle` – `Q₁ ⪯ Q₂`
* `hq` – same center

## Conclusion
* `E₁` lies in `E₂`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Q₁ ⪯ Q₂` about one center: the first ellipsoid lies in the second. -/
theorem Ellipsoid.construct_subset_of_le {E₁ E₂ : Ellipsoid n} (hle : (E₂.Q - E₁.Q).PosSemidef)
    (hq : E₁.q = E₂.q) : -- --- CONCL ---
    E₁.construct ⊆ E₂.construct := by -- --- PROOF ---
  rw [E₁.construct_eq_sqrt]
  -- `D^(1/2)` beside `G₁`
  set H : Mat ℝ n n := CFC.sqrt (E₂.Q - E₁.Q) with hH
  have hHH : H * Hᵀ = E₂.Q - E₁.Q :=
    (⟨E₂.Q - E₁.Q, 0, hle⟩ : Ellipsoid n).G_mul_transpose
  set F : Mat ℝ n (n + n) := Matrix.of fun i => Fin.append (fun j => E₁.G i j) (fun j => H i j)
    with hF
  have hFF : F * Fᵀ = E₂.Q := by
    have h1 := E₁.G_mul_transpose
    ext i k
    have e1 := congrFun (congrFun h1 i) k
    have e2 := congrFun (congrFun hHH i) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply] at e1 e2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hF, Matrix.of_apply, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
    rw [e1, e2]
    ring
  rw [E₂.construct_eq_of_factor F hFF]
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨Fin.append u 0, ?_, ?_⟩
  · -- the padding adds nothing to the length
    have hsq : ‖(Fin.append u 0 : Vec ℝ (n + n))‖₂ ^ 2 = ‖u‖₂ ^ 2 := by
      rw [norm₂_sq, norm₂_sq, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
      simp
    have h0 := norm₂_nonneg (Fin.append u 0 : Vec ℝ (n + n))
    have h1 := norm₂_nonneg u
    nlinarith
  · rw [hq]
    congr 1
    funext i
    simp only [Matrix.mulVec, dotProduct, hF, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
