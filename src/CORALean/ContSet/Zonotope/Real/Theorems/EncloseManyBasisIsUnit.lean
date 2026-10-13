import CORALean.ContSet.Zonotope.Real.Operations.EncloseManyBasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# `encloseMany`'s rotation is invertible

For a nonzero direction, `[newGen, axes without the dropped one]` has trivial kernel: the
dropped coordinate of the product is `newGen_dropped · y₀`, and `newGen_dropped` is the entry of
largest magnitude, hence nonzero; the other coordinates are then the remaining `y`.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.encloseManyBasis_isUnit (direction : Vec ℝ (m + 1)) (hd : direction ≠ 0) :
    IsUnit (Matrix.det (Zonotope.encloseManyBasis direction)) := by -- --- PROOF ---
  set s := (Real.sqrt (direction ⬝ᵥ direction))⁻¹ with hs
  set newGen : Vec ℝ (m + 1) := s • direction with hng
  set k0 := Zonotope.encloseManyDropped direction with hk0
  have hspec := (Finset.exists_max_image Finset.univ (fun k => |newGen k|)
    ⟨0, Finset.mem_univ _⟩).choose_spec
  have hmax : ∀ k, |newGen k| ≤ |newGen k0| := fun k => hspec.2 k (Finset.mem_univ _)
  obtain ⟨k1, hk1⟩ : ∃ k, direction k ≠ 0 := by
    by_contra h
    apply hd
    funext k
    by_contra hk
    exact h ⟨k, hk⟩
  -- the scale is positive, so `newGen` is nonzero where `direction` is
  have hspos : 0 < s := by
    rw [hs]
    refine inv_pos.mpr (Real.sqrt_pos.mpr ?_)
    refine lt_of_lt_of_le (mul_self_pos.mpr hk1) ?_
    exact Finset.single_le_sum (f := fun k => direction k * direction k)
      (fun k _ => mul_self_nonneg _) (Finset.mem_univ k1)
  have hk0ne : newGen k0 ≠ 0 := by
    have h1 : newGen k1 ≠ 0 := by
      simp only [hng, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hspos.ne' hk1
    intro h0
    have := hmax k1
    rw [h0, abs_zero] at this
    exact h1 (abs_nonpos_iff.mp this)
  -- a kernel vector of the rotation is zero
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hy0
  -- the component of the product at each row
  have hrow : ∀ i, newGen i * y 0 + ∑ j : Fin m,
      (if i = k0.succAbove j then (1 : ℝ) else 0) * y j.succ = 0 := by
    intro i
    have := congrFun hy i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at this
    exact this

  -- the dropped row sees only `newGen`
  have h0 : y 0 = 0 := by
    have := hrow k0
    have hsum : ∑ j : Fin m, (if k0 = k0.succAbove j then (1 : ℝ) else 0) * y j.succ = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [if_neg (Fin.succAbove_ne k0 j).symm, zero_mul]
    rw [hsum, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hk0ne
  have hrest : ∀ j : Fin m, y j.succ = 0 := by
    intro j
    have := hrow (k0.succAbove j)
    rw [h0, mul_zero, zero_add, Finset.sum_eq_single j] at this
    · simpa using this
    · intro j' _ hj'
      rw [if_neg (fun h => hj' (Fin.succAbove_right_injective h).symm), zero_mul]
    · simp
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hrest j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
