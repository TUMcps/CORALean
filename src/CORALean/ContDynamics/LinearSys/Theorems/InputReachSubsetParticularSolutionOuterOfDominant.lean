import CORALean.ContDynamics.LinearSys.Theorems.InputReachMemAddClosureConvexHull
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter

/-!
# Eq. (20) is sound when one point of `U₀` dominates the rest

[1, Prop. 11], eq. (20)'s soundness `P^U(Δt) ⊆ P̂^U(Δt)`, for `U₀` convex, closed and bounded
with a point `w*` whose coordinates bound every other point's in absolute value. Then
`E(Δt,η)ΔtU₀` is the box `|y_j| ≤ Σ_k |E_jk| Δt |w*_k|`: no point of `ΔtU₀` reaches further in
any coordinate than `Δt w*`, and a row of `M` scaled from `|E|` with the signs of `w*` reaches
every point of the box from `Δt w*` alone. A box is closed and convex, so the closed convex
hull `LinearSys.inputReach_mem_add_closure_convexHull` lands the tail in is the set itself.

[1]'s `U₀ = ⟨0, BG_u⟩` has such a point when the input is scalar (`U₀` a segment through `0`)
and when it is a box; in general it does not, and the general case is open (see `Prop. 11` on
[1]'s page).

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With a dominating point `w`, the interval product of `E` with `Δt • U` is the box
`|y_j| ≤ Σ_k |E_jk| Δt |w_k|`. -/
theorem aux_intervalMulVecSet_eq_box (E : Mat ℝ n n) {U : Set (Vec ℝ n)} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) {w : Vec ℝ n} (hw : w ∈ U) (hdom : ∀ v ∈ U, ∀ k, |v k| ≤ |w k|) :
    MatExp.intervalMulVecSet E (Δt • U)
      = {y | ∀ j, |y j| ≤ ∑ k, |E j k| * (Δt * |w k|)} := by -- --- PROOF ---
  ext y
  constructor
  · -- `|(M (Δt v))_j| ≤ Σ_k |M_jk| Δt |v_k| ≤ Σ_k |E_jk| Δt |w_k|`
    rintro ⟨M, hM, x, ⟨v, hv, rfl⟩, rfl⟩ j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hΔt]
    exact mul_le_mul (hM j k) (mul_le_mul_of_nonneg_left (hdom v hv k) hΔt)
      (mul_nonneg hΔt (abs_nonneg _)) (abs_nonneg _)
  · -- row `j` of `M` is `|E_j·|` with the signs of `w`, scaled by `y_j / s_j`
    intro hy
    set s : Fin n → ℝ := fun j => ∑ k, |E j k| * (Δt * |w k|)
    set σ : Fin n → ℝ := fun k => if 0 ≤ w k then 1 else -1
    have hσ : ∀ k, σ k * w k = |w k| := fun k => by
      by_cases h : 0 ≤ w k
      · simp [σ, h, abs_of_nonneg h]
      · simp [σ, h, abs_of_neg (not_le.1 h)]
    have hσ1 : ∀ k, |σ k| = 1 := fun k => by by_cases h : 0 ≤ w k <;> simp [σ, h]
    set M : Mat ℝ n n := fun j k => (y j / s j) * (|E j k| * σ k)
    refine ⟨M, fun j k => ?_, Δt • w, ⟨w, hw, rfl⟩, ?_⟩
    · -- `|y_j / s_j| ≤ 1`, or `s_j = 0` and the row is `0`
      have hq : |y j / s j| ≤ 1 := by
        rcases eq_or_lt_of_le (Finset.sum_nonneg fun k _ =>
          mul_nonneg (abs_nonneg (E j k)) (mul_nonneg hΔt (abs_nonneg (w k))) : 0 ≤ s j)
          with h | h
        · rw [show s j = 0 from h.symm, div_zero, abs_zero]; exact zero_le_one
        · rw [abs_div, abs_of_pos h]; exact (div_le_one h).2 (hy j)
      simp only [M, abs_mul, abs_abs, hσ1, mul_one]
      exact mul_le_of_le_one_left (abs_nonneg _) hq
    · funext j
      simp only [M, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have hrow : ∑ k, y j / s j * (|E j k| * σ k) * (Δt * w k) = y j / s j * s j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hσ k]; ring
      rw [hrow]
      rcases eq_or_ne (s j) 0 with h | h
      · have : |y j| ≤ 0 := h ▸ hy j
        simp [h, abs_nonpos_iff.1 this]
      · field_simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11], eq. (20): `P^U(Δt) ⊆ ⊕_{i≤η} ÃᵢU₀ ⊕ E(Δt,η)ΔtU₀` when some `w* ∈ U₀` has
`|w_k| ≤ |w*_k|` for every `w ∈ U₀` and every `k`. -/
theorem LinearSys.inputReach_subset_particularSolutionOuter_of_dominant (sys : LinearSys 𝕋 n)
    {U : S n} (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U)) {w : Vec ℝ n} (hw : w ∈ construct U)
    (hdom : ∀ v ∈ construct U, ∀ k, |v k| ≤ |w k|) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ) :
    sys.inputReach U Δt ⊆
      MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η := by -- --- PROOF ---
  set E := MatExp.expRemainderMat (toRealMat sys.A) Δt η
  set B : Set (Vec ℝ n) := {y | ∀ j, |y j| ≤ ∑ k, |E j k| * (Δt * |w k|)}
  have hEq := aux_intervalMulVecSet_eq_box E hΔt.le hw hdom
  -- the box is closed and convex, so it holds the closed convex hull of itself
  have hBconv : Convex ℝ B := by
    intro y hy z hz a b ha hb hab j
    calc |(a • y + b • z) j| ≤ a * |y j| + b * |z j| := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * _ + b * _ := add_le_add (mul_le_mul_of_nonneg_left (hy j) ha)
          (mul_le_mul_of_nonneg_left (hz j) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hBclosed : IsClosed B := by
    simp only [B, Set.setOf_forall]
    exact isClosed_iInter fun j =>
      isClosed_le ((continuous_apply j).abs) continuous_const
  -- bounded, as `inputReach_mem_add_closure_convexHull` asks of the remainder block
  have hBbdd : Bornology.IsBounded B := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2
      ⟨∑ j, ∑ k, |E j k| * (Δt * |w k|), fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg
      fun k _ => mul_nonneg (abs_nonneg _) (mul_nonneg hΔt.le (abs_nonneg _)))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact (hy j).trans (Finset.single_le_sum (f := fun j => ∑ k, |E j k| * (Δt * |w k|))
      (fun j _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (mul_nonneg hΔt.le (abs_nonneg _))) (Finset.mem_univ j))
  -- the tail is in the closed convex hull of the box, which is the box
  intro y hy
  obtain ⟨x, hx, t, ht, rfl⟩ := sys.inputReach_mem_add_closure_convexHull hconv hclosed hbdd hΔt η
    (by rw [hEq]; exact hBbdd) hy
  rw [hEq, (convexHull_eq_self.2 hBconv), hBclosed.closure_eq] at ht
  exact Set.add_mem_add hx (hEq ▸ ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
