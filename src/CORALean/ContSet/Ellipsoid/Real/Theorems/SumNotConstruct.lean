module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestSupport
public import CORALean.ContSet.Ellipsoid.Real.Theorems.NormPullbackEq
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The Minkowski sum of two ellipsoids is not an ellipsoid

[1, Sec. I (Fig. 1)]. The ellipses with shape matrices `diag(4, 1)` and `diag(1, 4)` have a
sum whose support function `√(ℓᵀQℓ) = ‖Gᵀℓ‖₂` would have to satisfy the parallelogram law, which
`ℓ ↦ √(ℓᵀQ₁ℓ) + √(ℓᵀQ₂ℓ)` breaks at `ℓ = (1, ±1)` against `e₁, e₂`: `20 + 20 ≠ 2·9 + 2·9`.
The statement quantifies over every ellipsoid of the plane, degenerate ones included.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* two nondegenerate ellipses exist whose sum is no ellipse

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise
open scoped MatrixOrder

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The functional `x ↦ d ⬝ᵥ x`. -/
noncomputable def aux_dotFun (d : Vec ℝ n) : Vec ℝ n →ₗ[ℝ] ℝ where
  toFun x := d ⬝ᵥ x
  map_add' x y := by simp [dotProduct_add]
  map_smul' r x := by simp [dotProduct_smul]

theorem aux_dualVec_dotFun (d : Vec ℝ n) : dualVec (aux_dotFun d) = d := by
  funext i
  simp [dualVec, aux_dotFun, dotProduct]

/-- The support value of a sum is the sum of the support values. -/
theorem aux_support_sum_eq (E E₁ E₂ : Ellipsoid n) (h : E₁.construct + E₂.construct = E.construct)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) : -- --- CONCL ---
    (E.supportBound c).val =
      (E₁.supportBound c).val + (E₂.supportBound c).val := by -- --- PROOF ---
  obtain ⟨⟨x, hx, hcx⟩, hub⟩ := E.isGreatest_support c
  obtain ⟨⟨x₁, hx₁, hcx₁⟩, hub₁⟩ := E₁.isGreatest_support c
  obtain ⟨⟨x₂, hx₂, hcx₂⟩, hub₂⟩ := E₂.isGreatest_support c
  apply le_antisymm
  · rw [← h] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [map_add] at hcx
    have h1 := hub₁ ⟨a, ha, rfl⟩
    have h2 := hub₂ ⟨b, hb, rfl⟩
    linarith
  · have : x₁ + x₂ ∈ E.construct := h ▸ Set.add_mem_add hx₁ hx₂
    have := hub ⟨_, this, rfl⟩
    rw [map_add] at this
    linarith

/-- `‖Gᵀd‖₂²` as a sum over the generators. -/
theorem aux_pullback_sq (E : Ellipsoid n) (d : Vec ℝ n) :
    ‖E.pullback (aux_dotFun d)‖₂ ^ 2 = ∑ j, (∑ i, E.G i j * d i) ^ 2 := by
  rw [norm₂_sq, Ellipsoid.pullback, aux_dualVec_dotFun]
  simp [Matrix.mulVec, dotProduct]

/-- The parallelogram law for the squared support lengths. -/
theorem aux_parallelogram (E : Ellipsoid n) (u v : Vec ℝ n) : -- --- CONCL ---
    ‖E.pullback (aux_dotFun (u + v))‖₂ ^ 2 + ‖E.pullback (aux_dotFun (u - v))‖₂ ^ 2
      = 2 * ‖E.pullback (aux_dotFun u)‖₂ ^ 2
        + 2 * ‖E.pullback (aux_dotFun v)‖₂ ^ 2 := by -- --- PROOF ---
  simp only [aux_pullback_sq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- `diag(4, 1)` is positive definite. -/
theorem aux_posDef_41 : (diagonal ![(4 : ℝ), 1]).PosDef := by
  rw [posDef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `diag(1, 4)` is positive definite. -/
theorem aux_posDef_14 : (diagonal ![(1 : ℝ), 4]).PosDef := by
  rw [posDef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- The first ellipse: semi-axes `2` and `1`. -/
noncomputable def aux_E₁ : Ellipsoid 2 := ⟨diagonal ![4, 1], 0, aux_posDef_41.posSemidef⟩

/-- The second ellipse: semi-axes `1` and `2`. -/
noncomputable def aux_E₂ : Ellipsoid 2 := ⟨diagonal ![1, 4], 0, aux_posDef_14.posSemidef⟩

/-- The first ellipse's support length. -/
theorem aux_len₁ (d : Vec ℝ 2) :
    ‖aux_E₁.pullback (aux_dotFun d)‖₂ = √((2 * d 0) ^ 2 + d 1 ^ 2) := by
  rw [Ellipsoid.norm₂_pullback, aux_dualVec_dotFun]
  congr 1
  simp [aux_E₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, diagonal]
  ring

/-- The second ellipse's support length. -/
theorem aux_len₂ (d : Vec ℝ 2) :
    ‖aux_E₂.pullback (aux_dotFun d)‖₂ = √(d 0 ^ 2 + (2 * d 1) ^ 2) := by
  rw [Ellipsoid.norm₂_pullback, aux_dualVec_dotFun]
  congr 1
  simp [aux_E₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, diagonal]
  ring

/-- The support length of the sum is the sum of the support lengths: the center cancels in
`d` and `-d`. -/
theorem aux_support_length_sum (d : Vec ℝ 2) (E : Ellipsoid 2)
    (h : aux_E₁.construct + aux_E₂.construct = E.construct) : -- --- CONCL ---
    ‖E.pullback (aux_dotFun d)‖₂ =
      ‖aux_E₁.pullback (aux_dotFun d)‖₂ + ‖aux_E₂.pullback (aux_dotFun d)‖₂ := by -- --- PROOF ---
  have h1 := aux_support_sum_eq E aux_E₁ aux_E₂ h (aux_dotFun d)
  have h2 := aux_support_sum_eq E aux_E₁ aux_E₂ h (aux_dotFun (-d))
  have hq₁ : aux_E₁.q = 0 := rfl
  have hq₂ : aux_E₂.q = 0 := rfl
  have hl : aux_dotFun (-d) E.q = -aux_dotFun d E.q := by
    show (-d) ⬝ᵥ E.q = -(d ⬝ᵥ E.q)
    exact neg_dotProduct _ _
  have hn : ∀ F : Ellipsoid 2, ‖F.pullback (aux_dotFun (-d))‖₂ = ‖F.pullback (aux_dotFun d)‖₂ := by
    intro F
    have : F.pullback (aux_dotFun (-d)) = (-1 : ℝ) • F.pullback (aux_dotFun d) := by
      simp [Ellipsoid.pullback, aux_dualVec_dotFun, Matrix.mulVec_neg]
    rw [this, norm₂_smul]
    simp
  simp only [Ellipsoid.supportBound, ← Ellipsoid.norm₂_pullback, hq₁, hq₂, map_zero, zero_add, hl,
    hn] at h1 h2
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. I (Fig. 1)]: the sum of two nondegenerate ellipses is no ellipsoid. -/
theorem Ellipsoid.exists_sum_not_construct : -- --- CONCL ---
    ∃ E₁ E₂ : Ellipsoid 2, E₁.Q.PosDef ∧ E₂.Q.PosDef ∧
      ∀ E : Ellipsoid 2, E₁.construct + E₂.construct ≠ E.construct := by -- --- PROOF ---
  refine ⟨aux_E₁, aux_E₂, aux_posDef_41, aux_posDef_14, fun E h => ?_⟩
  -- the squared lengths at `(1, 1)`, `(1, -1)`, `e₁`, `e₂` would obey the parallelogram law
  have hp := aux_parallelogram E ![1, 0] ![0, 1]
  have e1 := aux_support_length_sum ![1, 0] E h
  have e2 := aux_support_length_sum ![0, 1] E h
  have e3 := aux_support_length_sum (![1, 0] + ![0, 1]) E h
  have e4 := aux_support_length_sum (![1, 0] - ![0, 1]) E h
  rw [e3, e4, e1, e2] at hp
  simp only [aux_len₁, aux_len₂] at hp
  norm_num at hp
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h4 : √4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4] at hp
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
