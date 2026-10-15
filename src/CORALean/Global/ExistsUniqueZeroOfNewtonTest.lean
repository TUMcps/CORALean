module

public import CORALean.Global.Brouwer
public import CORALean.Global.MulVecInjectiveOfResidual
public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# A Newton test proves a unique zero in a ball

`g : ℝᵏ → ℝᵏ`, a center `c`, a radius `r` and a matrix `R`, an approximate inverse of the
Jacobian trusted for nothing. Between any two points of the sup-norm ball `B` of radius `r`
about `c`, `g` has a slope `J` (`g a - g a' = J (a - a')`) whose rows of `|1 - R J|` sum to at
most `qᵢ < 1`, and `qᵢ r + |(R g(c))ᵢ| ≤ r` in every coordinate. Then `g` has exactly one zero
in `B`.

This is Krawczyk's test, in the form that bounds the Krawczyk operator
`c - R g(c) + (1 - R J)(B - c)` by magnitudes. The map `φ a = a - R g(a)` takes `B` into itself,
since `φ a - c = (1 - R J)(a - c) - R g(c)`, and is `1`-Lipschitz on it, so Brouwer's theorem
(`exists_fixedPoint_of_isCompact_convex`) fixes a point, where `R g = 0`. `1 - R J` having rows
below `1` makes `R J` injective (`mulVec_injective_of_residual`), hence `R` invertible, and a
second zero `z'` would give `R J (z - z') = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coordinate of `M v` is at most the row's absolute sum times the sup norm of `v`. -/
theorem aux_abs_mulVec_le (M : Mat ℝ k k) (v : Vec ℝ k) (i : Fin k) :
    |(M *ᵥ v) i| ≤ (∑ j, |M i j|) * ‖v‖ := by -- --- PROOF ---
  calc |(M *ᵥ v) i| = |∑ j, M i j * v j| := rfl
    _ ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖v‖ := by rw [Finset.sum_mul]

/-- `R J` is injective when the rows of `|1 - R J|` sum below `1`. -/
theorem aux_injective (R J : Mat ℝ k k) (q : Vec ℝ k) (hJ : ∀ i, ∑ j, |(1 - R * J) i j| ≤ q i)
    (hq : ∀ i, q i < 1) : Function.Injective (R * J).mulVec :=
  mulVec_injective_of_residual 1 (R * J) fun i => by
    rw [Matrix.one_mul]; exact lt_of_le_of_lt (hJ i) (hq i)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A center, a radius and an approximate inverse `R` passing the test certify exactly one zero of
`g` in the closed sup-norm ball. -/
theorem existsUnique_zero_of_newtonTest (g : Vec ℝ k → Vec ℝ k) (c : Vec ℝ k) {r : ℝ}
    (hr : 0 ≤ r) (R : Mat ℝ k k) (q : Vec ℝ k)
    (hslope : ∀ a ∈ Metric.closedBall c r, ∀ a' ∈ Metric.closedBall c r,
      ∃ J : Mat ℝ k k, g a - g a' = J *ᵥ (a - a') ∧ ∀ i, ∑ j, |(1 - R * J) i j| ≤ q i)
    (hq : ∀ i, q i < 1) (hball : ∀ i, q i * r + |(R *ᵥ g c) i| ≤ r) :
    ∃! z, z ∈ Metric.closedBall c r ∧ g z = 0 := by -- --- PROOF ---
  have hc : c ∈ Metric.closedBall c r := Metric.mem_closedBall_self hr
  -- the Newton map, and its differences through a slope
  set φ : Vec ℝ k → Vec ℝ k := fun a => a - R *ᵥ g a with hφ
  have hdiff : ∀ a a' (J : Mat ℝ k k), g a - g a' = J *ᵥ (a - a') →
      φ a - φ a' = (1 - R * J) *ᵥ (a - a') := by
    intro a a' J hJ
    have : φ a - φ a' = (a - a') - R *ᵥ (g a - g a') := by
      simp only [hφ, Matrix.mulVec_sub]; abel
    rw [this, hJ, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  -- `q` is nonnegative wherever a slope exists, so everywhere
  obtain ⟨J₀, -, hJ₀⟩ := hslope c hc c hc
  have hq0 : ∀ i, 0 ≤ q i := fun i =>
    le_trans (Finset.sum_nonneg fun j _ => abs_nonneg _) (hJ₀ i)
  -- `φ` is `1`-Lipschitz on the ball
  have hlip : ∀ a ∈ Metric.closedBall c r, ∀ a' ∈ Metric.closedBall c r,
      ‖φ a - φ a'‖ ≤ ‖a - a'‖ := by
    intro a ha a' ha'
    obtain ⟨J, hJ, hJq⟩ := hslope a ha a' ha'
    rw [hdiff a a' J hJ]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine le_trans (aux_abs_mulVec_le _ _ i) ?_
    exact le_trans (mul_le_mul_of_nonneg_right (hJq i) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (hq i).le)
  have hcont : ContinuousOn φ (Metric.closedBall c r) :=
    (LipschitzOnWith.of_dist_le_mul (K := 1) fun a ha a' ha' => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
      exact hlip a ha a' ha').continuousOn
  -- `φ` maps the ball into itself
  have hmaps : Set.MapsTo φ (Metric.closedBall c r) (Metric.closedBall c r) := by
    intro a ha
    obtain ⟨J, hJ, hJq⟩ := hslope a ha c hc
    have hac : ‖a - c‖ ≤ r := by rw [← dist_eq_norm]; exact ha
    have heq : φ a - c = (1 - R * J) *ᵥ (a - c) - R *ᵥ g c := by
      rw [← hdiff a c J hJ]; simp only [hφ]; abel
    rw [Metric.mem_closedBall, dist_eq_norm, heq]
    refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    refine le_trans (abs_sub _ _) (le_trans (add_le_add ?_ le_rfl) (hball i))
    refine le_trans (aux_abs_mulVec_le _ _ i) ?_
    exact mul_le_mul (hJq i) hac (norm_nonneg _) (hq0 i)
  -- Brouwer gives a fixed point, where `R g = 0`
  obtain ⟨z, hz, hfix⟩ := exists_fixedPoint_of_isCompact_convex (isCompact_closedBall c r)
    (convex_closedBall c r) ⟨c, hc⟩ hcont hmaps
  have hRg : R *ᵥ g z = 0 := by
    have : z - R *ᵥ g z = z := hfix
    simpa using this
  -- `R` is invertible: `R J₀` is
  have hRJ : IsUnit (R * J₀) :=
    (Matrix.mulVec_injective_iff_isUnit).mp (aux_injective R J₀ q hJ₀ hq)
  have hR : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det] at hRJ ⊢
    rw [Matrix.det_mul] at hRJ
    exact isUnit_of_mul_isUnit_left hRJ
  have hRinj : Function.Injective R.mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr hR
  refine ⟨z, ⟨hz, hRinj (by rw [hRg, Matrix.mulVec_zero])⟩, ?_⟩
  -- a second zero is the first: `R J` is injective for the slope between them
  rintro z' ⟨hz', hg'⟩
  obtain ⟨J, hJ, hJq⟩ := hslope z' hz' z hz
  have h0 : (R * J) *ᵥ (z' - z) = (R * J) *ᵥ 0 := by
    rw [← Matrix.mulVec_mulVec, ← hJ, hg', (show g z = 0 from hRinj (by
      rw [hRg, Matrix.mulVec_zero])), sub_self, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact sub_eq_zero.mp (aux_injective R J q hJq hq h0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
