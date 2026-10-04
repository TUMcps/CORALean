import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A checked approximate inverse places a vector in a basis, with a bound

If `H P = 1 - K` where every row of `K` sums, in absolute value, to at most `q ≤ 1/2`, then `P` is
invertible and the coordinates `w = P⁻¹ d` of a vector `d` in the basis satisfy `|wᵢ| ≤ 2B` whenever
`|(H d)ᵢ| ≤ B`. Nothing says `H` is the inverse of `P`: the certificate `K` small is what makes it
close enough to be used as one, and that is all a float layer can check.

The invertibility is the contraction at work: `P x = 0` gives `x = K x`, and the coordinate of
largest magnitude then shrinks by `q`. The bound is the same step on `w = H d + K w`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix with small absolute row sums contracts the sup norm. -/
theorem Zonotope.aux_contract {K : Mat ℝ n n} {q : ℝ} (hK : ∀ i, ∑ j, |K i j| ≤ q)
    (x : Vec ℝ n) {M : ℝ} (hM : 0 ≤ M) (hx : ∀ j, |x j| ≤ M) (i : Fin n) :
    |(K *ᵥ x) i| ≤ q * M := by -- --- PROOF ---
  calc |(K *ᵥ x) i| = |∑ j, K i j * x j| := rfl
    _ ≤ ∑ j, |K i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |K i j| * M := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |K i j|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ q * M := mul_le_mul_of_nonneg_right (hK i) hM

/-- `P x = 0` leaves only `x = 0`, the largest coordinate of `x = K x` being at most half of
itself. -/
theorem Zonotope.aux_injective (Pm Hm : Mat ℝ n n) {q : ℝ} (hq : q ≤ 1 / 2)
    (hK : ∀ i, ∑ j, |(1 - Hm * Pm) i j| ≤ q) (x : Vec ℝ n) (hx : Pm *ᵥ x = 0) :
    x = 0 := by -- --- PROOF ---
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact funext fun i => (IsEmpty.false i).elim
  -- `x = K x`, as `H (P x) = 0`
  have hxK : x = (1 - Hm * Pm) *ᵥ x := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hx, mulVec_zero, sub_zero]
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
  have h1 := Zonotope.aux_contract hK x (abs_nonneg _) (fun j => hk j (Finset.mem_univ j)) k
  rw [← hxK] at h1
  have h0 : |x k| ≤ 0 := by nlinarith [abs_nonneg (x k)]
  exact funext fun j => abs_nonpos_iff.mp (le_trans (hk j (Finset.mem_univ j)) h0)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.basis_reach (Pm Hm : Mat ℝ n n) {q B : ℝ} (hq : q ≤ 1 / 2)
    (hK : ∀ i, ∑ j, |(1 - Hm * Pm) i j| ≤ q) (d : Vec ℝ n) (hd : ∀ i, |(Hm *ᵥ d) i| ≤ B) :
    ∃ w : Vec ℝ n, Pm *ᵥ w = d ∧ ∀ k, |w k| ≤ 2 * B := by -- --- PROOF ---
  -- `P` is invertible: injective on vectors, and square
  have hinj : Function.Injective Pm.mulVec := fun x y hxy =>
    sub_eq_zero.mp (Zonotope.aux_injective Pm Hm hq hK (x - y) (by rw [mulVec_sub, hxy, sub_self]))
  have hU : IsUnit Pm := mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit Pm.det := (isUnit_iff_isUnit_det Pm).mp hU
  have hw : Pm *ᵥ (Pm⁻¹ *ᵥ d) = d := by
    rw [mulVec_mulVec, mul_nonsing_inv Pm hdet, one_mulVec]
  refine ⟨Pm⁻¹ *ᵥ d, hw, ?_⟩
  set w := Pm⁻¹ *ᵥ d with hwdef
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact fun k => (IsEmpty.false k).elim
  -- `w = H d + K w`, and the largest coordinate of `K w` is at most half of it
  have hwK : w = Hm *ᵥ d + (1 - Hm * Pm) *ᵥ w := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hw]
    abel
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => |w i|) Finset.univ_nonempty
  have h1 := Zonotope.aux_contract hK w (abs_nonneg _) (fun j => hk j (Finset.mem_univ j)) k
  have h2 : |w k| ≤ |(Hm *ᵥ d) k| + |((1 - Hm * Pm) *ᵥ w) k| := by
    calc |w k| = |(Hm *ᵥ d) k + ((1 - Hm * Pm) *ᵥ w) k| := by
          conv_lhs => rw [hwK]
          rfl
      _ ≤ _ := abs_add_le _ _
  have h3 := hd k
  have h4 : |w k| ≤ 2 * B := by nlinarith [abs_nonneg (w k)]
  exact fun j => le_trans (hk j (Finset.mem_univ j)) h4

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
