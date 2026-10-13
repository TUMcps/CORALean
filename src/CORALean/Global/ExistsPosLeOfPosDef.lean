module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# A positive definite form is bounded below by a multiple of the square

A real `M ≻ 0` has some `ε > 0` with `ε xᵀx ≤ xᵀ M x` for every `x`: the margin a strict matrix
inequality leaves, which the observer papers spend without naming (a strict `H∞` bound, the
scalars `α₁ I ≺ P` of a Lyapunov argument). The form attains its minimum `ε` on the compact
unit sphere `xᵀx = 1`, positive there, and scales by `xᵀx` off it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_pos_le_of_posDef (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    ∃ ε > 0, ∀ x : ι → ℝ, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by -- --- PROOF ---
  have hpos := (posDef_iff_dotProduct_mulVec.mp hM).2
  set S : Set (ι → ℝ) := {x | x ⬝ᵥ x = 1} with hSdef
  -- a nonzero vector, rescaled onto the sphere
  have hscale : ∀ x : ι → ℝ, x ≠ 0 →
      0 < x ⬝ᵥ x ∧ (Real.sqrt (x ⬝ᵥ x))⁻¹ • x ∈ S := fun x hx => by
    have h0 : 0 < x ⬝ᵥ x := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i) :
        (0 : ℝ) ≤ ∑ i, x i * x i) with h | h
      · exact h
      · exfalso
        refine hx (funext fun i => ?_)
        have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).mp h.symm i
          (Finset.mem_univ _)
        simpa using this
    refine ⟨h0, ?_⟩
    show _ ⬝ᵥ _ = 1
    rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt h0.le, inv_mul_cancel₀ h0.ne']
  by_cases hS : S.Nonempty
  · -- the sphere is compact: closed, and inside the unit ball of the sup norm
    have hclosed : IsClosed S := isClosed_eq (by simp only [dotProduct]; fun_prop) continuous_const
    have hbdd : Bornology.IsBounded S := by
      refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset fun x hx => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have hle : x i * x i ≤ x ⬝ᵥ x :=
        Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
          (Finset.mem_univ i)
      rw [hx] at hle
      rw [Real.norm_eq_abs]
      nlinarith [abs_mul_abs_self (x i), abs_nonneg (x i)]
    -- the form attains its minimum `ε > 0` on the sphere
    have hcpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
    obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hS
      (Continuous.continuousOn (f := fun x : ι → ℝ => x ⬝ᵥ (M *ᵥ x))
        (by simp only [dotProduct, mulVec]; fun_prop))
    have hx₀0 : x₀ ≠ 0 := fun h => by
      have : x₀ ⬝ᵥ x₀ = 1 := hx₀
      simp [h] at this
    have hε := hpos hx₀0
    rw [star_trivial] at hε
    refine ⟨_, hε, fun x => ?_⟩
    -- every other vector is a multiple of a unit one
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨h0, hu⟩ := hscale x hx
    have hm := hmin hu
    set t := Real.sqrt (x ⬝ᵥ x)
    have ht : 0 < t := Real.sqrt_pos.mpr h0
    -- the form scales by `t²` from the sphere, and `t² = xᵀx`
    have hform : x ⬝ᵥ (M *ᵥ x) = t ^ 2 * ((t⁻¹ • x) ⬝ᵥ (M *ᵥ (t⁻¹ • x))) := by
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      field_simp
    have ht2 : t ^ 2 = x ⬝ᵥ x := Real.sq_sqrt h0.le
    simp only [Set.mem_setOf_eq] at hm
    rw [hform, ← ht2, mul_comm]
    exact mul_le_mul_of_nonneg_left hm (sq_nonneg t)
  · -- no unit vector: every vector is zero
    refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    exact absurd ⟨_, (hscale x hx).2⟩ hS

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
