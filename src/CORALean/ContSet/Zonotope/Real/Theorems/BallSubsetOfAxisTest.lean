import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.EuclideanNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# A ball inside a zonotope, from points on the axes

[1, Lemma 5]: if `ν eᵢ` lies in the zonotope for every `i`, measured from the centre, then the
ball of radius `√(ν²/n)` around the centre does, so `⌊Z⌋² ≥ ν²/n`. The coefficients of the `n`
test points combine: `x = ∑ (xᵢ/ν) ν eᵢ`, and `∑ |xᵢ|/ν ≤ √n ‖x‖₂ / ν ≤ 1` keeps the combined
coefficients in the box. The printed test checks `ν eᵢ ∈ Z` itself, which is the statement only
for a zonotope centred at the origin (`ball_subset_of_axis_test_counterexample`). The printed
proof calls the hull of `±ν eᵢ` a rotated hypercube; for `n ≥ 3` it is a cross-polytope, whose
inscribed ball has the same radius `ν/√n`. The test is Goffin's, [2, Eq. 17], and the ball it gives
[2, Eq. 18]: `conv{±γ eᵢ} ⊇ E(γ²/n, 0)`, at the centre `0` the paper assumes and the radius
`γ = 1/√(n(1+ε))` of [2, Sec. 4.4].

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ball_subset_of_axis_test (Z : Zonotope (Vec ℝ n)) {ν : ℝ} (hν : 0 ≤ ν)
    (htest : ∀ i : Fin n, Z.c + ν • (Pi.single i 1 : Vec ℝ n) ∈ Z.construct) :
    ∀ x : Vec ℝ n, ‖x‖₂ ≤ √(ν ^ 2 / n) → Z.c + x ∈ Z.construct := by -- --- PROOF ---
  intro x hx
  rcases hν.eq_or_lt with rfl | hνpos
  -- `ν = 0`: the ball is the centre
  · have hx0 : x = 0 := by
      have : ‖x‖₂ ≤ 0 := by simpa using hx
      rw [← dotProduct_self_eq_zero, dotProduct_self]
      nlinarith [norm₂_nonneg x]
    exact ⟨0, fun _ => by simp, by simp [hx0]⟩
  choose β hβ hβeq using htest
  -- `‖x‖₁ ≤ √n ‖x‖₂ ≤ ν`
  have hl1 : ∑ i, |x i| ≤ ν := by
    have hcs : (∑ i, 1 * |x i|) ^ 2 ≤ (∑ _i : Fin n, (1 : ℝ) ^ 2) * ∑ i, |x i| ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at hcs
    have hx2 : ∑ i, x i ^ 2 ≤ ν ^ 2 / n := by
      rw [← norm₂_sq]
      calc ‖x‖₂ ^ 2 ≤ √(ν ^ 2 / n) ^ 2 := pow_le_pow_left₀ (norm₂_nonneg x) hx 2
        _ = ν ^ 2 / n := Real.sq_sqrt (by positivity)
    have hsq : (∑ i, |x i|) ^ 2 ≤ ν ^ 2 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
        positivity
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        calc (∑ i, |x i|) ^ 2 ≤ n * ∑ i, x i ^ 2 := hcs
          _ ≤ n * (ν ^ 2 / n) := mul_le_mul_of_nonneg_left hx2 hn'.le
          _ = ν ^ 2 := by field_simp
    exact abs_le_of_sq_le_sq' hsq hνpos.le |>.2
  -- the combined coefficients
  refine ⟨fun j => ∑ i, (x i / ν) * β i j, fun j => ?_, ?_⟩
  · calc |∑ i, (x i / ν) * β i j| ≤ ∑ i, |x i / ν| * |β i j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
      _ ≤ ∑ i, |x i| / ν := Finset.sum_le_sum fun i _ => by
          rw [abs_div, abs_of_pos hνpos]
          exact mul_le_of_le_one_right (by positivity) (hβ i j)
      _ = (∑ i, |x i|) / ν := (Finset.sum_div _ _ _).symm
      _ ≤ 1 := (div_le_one hνpos).mpr hl1
  · -- `∑ⱼ (∑ᵢ (xᵢ/ν) βᵢⱼ) gⱼ = ∑ᵢ (xᵢ/ν) ν eᵢ = x`
    have hx : x = ∑ i, (x i / ν) • (ν • (Pi.single i 1 : Vec ℝ n)) := by
      funext a
      simp [Finset.sum_apply, Pi.single_apply, div_mul_cancel₀ _ hνpos.ne']
    have hcomb : ∀ i, ν • (Pi.single i 1 : Vec ℝ n) = ∑ j, β i j • Z.G j := fun i =>
      add_left_cancel (hβeq i)
    congr 1
    conv_lhs => rw [hx]
    simp only [hcomb, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
