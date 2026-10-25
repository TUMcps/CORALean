module

public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHinfLmi
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The dissipation inequality of the `H∞` design

The step of the proof of [1, Thm. 1] from its Eq. 16 to its Eq. 17: if `P ≻ 0` and the
inequality Eq. 16 holds, then at `L = P⁻¹ Y`, `A_e = A - LC`, for every `e`, `w`, `v`
`(A_e e + E w - L F v)ᵀ P (A_e e + E w - L F v) + eᵀe - eᵀPe - γ²(wᵀw + vᵀv) ≤ -ε (eᵀe + wᵀw + vᵀv)`
for some `ε > 0`. The Schur complement of the block `P` (`posDef_schur_of_fromBlocks`) is its
Eq. 18, and a positive definite form has a margin (`aux_exists_pos_le_of_posDef`); that margin is
what makes the `H∞` bound of [1, Thm. 1] strict.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – disturbance matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Y` – gain variable
* `γ` – attenuation level

## Hypotheses
* `hP` – Lyapunov matrix positive definite
* `h` – the design inequality holds

## Conclusion
* the dissipation inequality holds with a positive margin

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {ι : Type} [Fintype ι]

/-- A positive definite form is bounded below by a multiple of the square. -/
theorem aux_exists_pos_le_of_posDef (M : Matrix ι ι ℝ) (hM : M.PosDef) : -- --- CONCL ---
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

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.dissipation_of_hinfLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ : ℝ) (hP : P.PosDef)
    (h : LinearSysDT.IsHinfLmi A C E F P Y γ) : -- --- CONCL ---
    ∃ ε > 0, ∀ (a : Vec ℝ n) (b : Vec ℝ nw) (c : Vec ℝ nv),
      let q := (A - P⁻¹ * Y * C) *ᵥ a + E *ᵥ b - (P⁻¹ * Y * F) *ᵥ c
      q ⬝ᵥ (P *ᵥ q) + a ⬝ᵥ a - a ⬝ᵥ (P *ᵥ a) - γ ^ 2 * (b ⬝ᵥ b + c ⬝ᵥ c) ≤
        -ε * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c) := by -- --- PROOF ---
  haveI : Invertible P := hP.isUnit.invertible
  set TL : Matrix (Fin n ⊕ (Fin nw ⊕ Fin nv)) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromBlocks (1 - P) 0 0 (fromBlocks (-(γ ^ 2) • 1) 0 0 (-(γ ^ 2) • 1)) with hTL
  set R : Matrix (Fin n) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromCols (P * A - Y * C) (fromCols (P * E) (-(Y * F))) with hR
  -- Eq. 18 of [1, Thm. 1]: the Schur complement of the block `P`
  have hneg : -(fromBlocks TL Rᵀ R (-P)) = fromBlocks (-TL) (-Rᵀ) (-Rᵀ)ᵀ P := by
    rw [fromBlocks_neg, transpose_neg, transpose_transpose, neg_neg]
  have hS := posDef_schur_of_fromBlocks (-TL) (-Rᵀ) hP (hneg ▸ h)
  obtain ⟨ε, hε, hle⟩ := aux_exists_pos_le_of_posDef _ hS
  refine ⟨ε, hε, fun a b c => ?_⟩
  intro q
  have hPT : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  -- `R (a, b, c) = P q`, the gain `L = P⁻¹ Y` undone
  have hRq : R *ᵥ Sum.elim a (Sum.elim b c) = P *ᵥ q := by
    have hPL : P * (P⁻¹ * Y) = Y := by
      rw [← Matrix.mul_assoc, mul_inv_of_invertible, Matrix.one_mul]
    simp only [hR, q, fromCols_mulVec_sumElim, mulVec_add, mulVec_sub, mulVec_mulVec,
      Matrix.mul_sub, ← Matrix.mul_assoc, hPL, neg_mulVec]
    abel
  -- the Schur term is `qᵀ P q`
  have hquad : Sum.elim a (Sum.elim b c) ⬝ᵥ ((-Rᵀ * P⁻¹ * (-Rᵀ)ᵀ) *ᵥ Sum.elim a (Sum.elim b c))
      = q ⬝ᵥ (P *ᵥ q) := by
    simp only [transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hRq, dotProduct_mulVec, vecMul_transpose, hRq,
      mulVec_mulVec, inv_mul_of_invertible, one_mulVec, dotProduct_comm]
  -- the diagonal blocks give `aᵀ(P - I)a + γ²(bᵀb + cᵀc)`
  have hTLq : Sum.elim a (Sum.elim b c) ⬝ᵥ ((-TL) *ᵥ Sum.elim a (Sum.elim b c)) =
      a ⬝ᵥ (P *ᵥ a) - a ⬝ᵥ a + γ ^ 2 * (b ⬝ᵥ b + c ⬝ᵥ c) := by
    simp only [hTL, neg_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      zero_mulVec, add_zero, zero_add, dotProduct_neg, sumElim_dotProduct_sumElim, sub_mulVec,
      one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, neg_smul,
      dotProduct_neg]
    ring
  have hξ := hle (Sum.elim a (Sum.elim b c))
  rw [sub_mulVec, dotProduct_sub, hTLq, hquad, sumElim_dotProduct_sumElim,
    sumElim_dotProduct_sumElim] at hξ
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
