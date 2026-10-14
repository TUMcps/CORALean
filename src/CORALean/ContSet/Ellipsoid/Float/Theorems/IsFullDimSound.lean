module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsFullDim
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsFullDimIff
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `Ellipsoid.isFullDim` proves an interior point

Read as reals, `G H` is strictly diagonally dominant, so its determinant is not zero
(`Matrix.det_ne_zero_of_sum_row_lt_diag`) and its rank is `n`; `rank (G H) ≤ rank G ≤ n` makes
`rank G = n`, which is a nonempty interior of the nominal ellipsoid
(`CORALean.Real.Ellipsoid.isFullDim_iff`). Adding the error box's lower corner, a member of the
nonempty box, keeps an interior point (`subset_interior_add_left`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over all indices but `k` is the sum with the `k`-th term replaced by zero. -/
theorem Ellipsoid.aux_sum_erase_eq {m : ℕ} (f : Fin m → ℝ) (k : Fin m) :
    ∑ j ∈ Finset.univ.erase k, f j = ∑ j, if j = k then 0 else f j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]

/-- The checked rows make the real product `G H` strictly diagonally dominant. -/
theorem Ellipsoid.aux_dominant {E : Ellipsoid 𝕋 n} {H : Mat 𝕋 E.k n}
    (h : ∀ i, ltStrict (sumUp fun l => if l = i then zero else
        maximum (dotUp (fun j => E.G i j) (fun j => H j l))
          (neg (dotDown (fun j => E.G i j) (fun j => H j l))))
      (dotDown (fun j => E.G i j) (fun j => H j i)) = true) (k : Fin n) :
    ∑ j ∈ Finset.univ.erase k, ‖(toRealMat E.G * toRealMat H) k j‖
      < ‖(toRealMat E.G * toRealMat H) k k‖ := by -- --- PROOF ---
  have hentry : ∀ i l, (toRealMat E.G * toRealMat H) i l
      = ∑ j, toReal (E.G i j) * toReal (H j l) := fun i l => by
    simp [Matrix.mul_apply, toRealMat]
  -- each off-diagonal magnitude is below its rounded bound
  have hmag : ∀ l, (if l = k then (0 : ℝ) else |(toRealMat E.G * toRealMat H) k l|)
      ≤ toReal (if l = k then (zero : 𝕋) else maximum (dotUp (fun j => E.G k j) (fun j => H j l))
          (neg (dotDown (fun j => E.G k j) (fun j => H j l)))) := by
    intro l
    by_cases hl : l = k
    · simp [hl, toReal_zero]
    · rw [if_neg hl, if_neg hl, toReal_maximum, toReal_neg, hentry]
      have d₁ := le_dotUp (fun j => E.G k j) (fun j => H j l)
      have d₂ := dotDown_le (fun j => E.G k j) (fun j => H j l)
      have m₁ := le_max_left (toReal (dotUp (fun j => E.G k j) (fun j => H j l)))
        (-toReal (dotDown (fun j => E.G k j) (fun j => H j l)))
      have m₂ := le_max_right (toReal (dotUp (fun j => E.G k j) (fun j => H j l)))
        (-toReal (dotDown (fun j => E.G k j) (fun j => H j l)))
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the off-diagonal sum, the certified gap and the diagonal's lower bound
  have hsum := le_trans (Finset.sum_le_sum fun l _ => hmag l) (sum_le_sumUp _)
  have hgap := toReal_lt_of_ltStrict (h k)
  have hdiag := dotDown_le (fun j => E.G k j) (fun j => H j k)
  rw [← hentry] at hdiag
  simp only [Real.norm_eq_abs]
  rw [Ellipsoid.aux_sum_erase_eq (fun j => |(toRealMat E.G * toRealMat H) k j|) k]
  exact lt_of_lt_of_le (lt_of_le_of_lt hsum hgap) (le_trans hdiag (le_abs_self _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isFullDim_sound {E : Ellipsoid 𝕋 n} {H : Mat 𝕋 E.k n}
    (h : E.isFullDim H = true) : (interior E.construct).Nonempty := by -- --- PROOF ---
  simp only [Ellipsoid.isFullDim, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true] at h
  -- `G H` is invertible, so `G` has full row rank
  have hdet := det_ne_zero_of_sum_row_lt_diag
    (Ellipsoid.aux_dominant (fun i => (h i).1))
  have hunit : IsUnit (toRealMat E.G * toRealMat H) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrank : (toRealMat E.G).rank = n := by
    refine le_antisymm (Matrix.rank_le_height _) ?_
    have := Matrix.rank_mul_le_left (toRealMat E.G) (toRealMat H)
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at this
    exact this
  -- an interior point of the nominal ellipsoid, moved by a member of the box
  obtain ⟨x, hx⟩ := (CORALean.Real.Ellipsoid.isFullDim_iff (nominal E)).mpr hrank
  have he : (fun i => toReal (E.I_error.inf i)) ∈ E.I_error.construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (h i).2⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
