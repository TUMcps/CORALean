module

public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMemAddClosureConvexHull
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsParticularTailEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuterCorrelated
public import CORALean.Global.EuclideanHausdorffDist
public import CORALean.Global.Norm2MulVecLeErrOfMemClosureConvexHull

@[expose] public section

/-!
# [1, Prop. 11] without eq. (20)'s soundness

[1, Prop. 11] bounds `d_H(e^{At_k}P^U(Δt), e^{At_k}P̂^U(Δt))` by `Δε^U_k` of eq. (25), and its proof
uses eq. (20)'s soundness `P^U(Δt) ⊆ P̂^U(Δt)`, which [1] cites and does not prove.
`MatExp.hausdorffDist₂_particularSolution_le` is that proof with the soundness as a hypothesis. This
file proves the bound without it, for the input set [1]'s Alg. 1 has: `U₀` convex, closed, bounded
and containing `0`. From an exact point, the outer set has the point that drops the tail:
`P^U(Δt) ∋ x + t` with `x ∈ ⊕_{i≤η}ÃᵢU₀` and `t` in the closed convex hull of `E(Δt,η)ΔtU₀`, and
`x + 0 ∈ P̂^U(Δt)`. The gap `e^{At_k}t` is bounded by `err(e^{At_k}P̂^U_∞(Δt))`: `err` reads only
each coordinate's extreme values, the same over a set and its closed convex hull.

## Inputs
* `sys` – linear system
* `tk` – step start time
* `U` – input set
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `h0` – origin in the input set
* `hΔt` – step length positive

## Conclusion
* the propagated Hausdorff distance is at most the particular solution error

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A uniform `‖·‖₂` bound is boundedness. -/
private theorem aux_hd_isBounded_of_norm₂_le {T : Set (Vec ℝ n)} {r : ℝ} (h : ∀ y ∈ T, ‖y‖₂ ≤ r) :
    Bornology.IsBounded T := by
  refine isBounded_iff_forall_norm_le.mpr ⟨max r 0, fun y hy => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_max_right r 0)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact ((abs_le_norm₂ y i).trans (h y hy)).trans (le_max_left r 0)

/-- Eq. (20)'s order-`0` block split off: `P̂^U(Δt) = ΔtU₀ ⊕ P̂^U_∞(Δt)`. -/
private theorem aux_hd_mem_outer_zero {A : Mat ℝ n n} {U0 : Set (Vec ℝ n)} {Δt : ℝ} {η : ℕ}
    {y : Vec ℝ n} (hy : y ∈ MatExp.particularSolutionOuter A U0 0 Δt η) : -- --- CONCL ---
    ∃ x₀ ∈ U0, ∃ r ∈ MatExp.particularSolutionOuter A U0 1 Δt η,
      y = Δt • x₀ + r := by -- --- PROOF ---
  rw [MatExp.particularSolutionOuter, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos η),
    add_assoc, Set.mem_add] at hy
  obtain ⟨a, ha, r, hr, rfl⟩ := hy
  obtain ⟨x₀, hx₀, rfl⟩ := ha
  refine ⟨x₀, hx₀, r, hr, ?_⟩
  congr 1
  simp only [MatExp.particularCoeff, pow_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
  norm_num

/-- The gap between the constant input's point at `x₀` and `Δtx₀` is in eq. (25)'s correlated
set. -/
private theorem aux_hd_mem_correlated (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)} {Δt : ℝ} (hΔt : 0 < Δt)
    (η : ℕ) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ U0) : -- --- CONCL ---
    (MatExp.expIntegral A Δt - MatExp.particularCoeff A Δt 0).mulVec x₀
      ∈ MatExp.particularSolutionOuterCorrelated A U0 1 Δt η := by -- --- PROOF ---
  set T := MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i
    with hT
  have hsplit : MatExp.expIntegral A Δt - MatExp.particularCoeff A Δt 0
      = MatExp.particularCoeffSum A Δt 1 η + T := by
    rw [hT, MatExp.particularCoeffSum, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos η)]
    abel
  -- the tail, divided by `Δt`, is an admissible value of the interval matrix `[-E,E]`
  have hE : ∀ j k, |(Δt⁻¹ • T) j k| ≤ |(MatExp.expRemainderMat A Δt η) j k| := by
    intro j k
    have hb : |T j k| ≤ Δt * (MatExp.expRemainderMat A Δt η) j k :=
      MatExp.abs_particularTail_entry_le A hΔt.le η j k
    have h0 : (0:ℝ) ≤ Δt * (MatExp.expRemainderMat A Δt η) j k := (abs_nonneg _).trans hb
    have hEnn : (0:ℝ) ≤ (MatExp.expRemainderMat A Δt η) j k := by nlinarith [h0, hΔt]
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hΔt),
      abs_of_nonneg hEnn]
    calc Δt⁻¹ * |T j k| ≤ Δt⁻¹ * (Δt * (MatExp.expRemainderMat A Δt η) j k) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (MatExp.expRemainderMat A Δt η) j k := by field_simp
  rw [hsplit, Matrix.add_mulVec, MatExp.particularSolutionOuterCorrelated]
  refine Set.add_mem_add (Set.mem_image_of_mem _ hx₀) ⟨Δt⁻¹ • T, hE, Δt • x₀,
    Set.smul_mem_smul_set hx₀, ?_⟩
  show (Δt⁻¹ • T) *ᵥ (Δt • x₀) = T *ᵥ x₀
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hΔt.ne', one_smul]

/-- The triangle inequality on a difference. -/
private theorem aux_hd_norm₂_sub_le (x y : Vec ℝ n) : ‖x - y‖₂ ≤ ‖x‖₂ + ‖y‖₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ y]
  refine (norm₂_add_le _ _).trans_eq ?_
  rw [norm₂_smul]
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11]: `d_H(e^{At_k}P^U(Δt), e^{At_k}P̂^U(Δt)) ≤ Δε^U_k(Δt,η)` of eq. (25), for `U₀`
convex, closed, bounded and containing `0`, with no hypothesis on eq. (20). -/
theorem LinearSys.hausdorffDist₂_inputReach_le_of_convex (sys : LinearSys 𝕋 n) (tk : ℝ)
    {U : S n} (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U) {Δt : ℝ}
    (hΔt : 0 < Δt) (η : ℕ) : -- --- CONCL ---
    hausdorffDist₂
        ((fun x => (exp (tk • toRealMat sys.A)).mulVec x) '' sys.inputReach U Δt)
        ((fun x => (exp (tk • toRealMat sys.A)).mulVec x)
          '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
      ≤ MatExp.particularSolutionError (toRealMat sys.A) tk (construct U) Δt
        η := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set U0 := construct U with hU0
  set M := exp (tk • A) with hM
  set Eset := MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0) with hEset
  set O1 := MatExp.particularSolutionOuter A U0 1 Δt η with hO1
  -- `0` is in every block, so the remainder block sits inside `P̂^U_∞(Δt)`
  have hE0 : (0 : Vec ℝ n) ∈ Eset :=
    ⟨0, fun j k => by simp, 0, by simpa using Set.smul_mem_smul_set (a := Δt) h0, by simp⟩
  have hsum0 : ∀ i0, (0 : Vec ℝ n) ∈ ∑ i ∈ Finset.Ico i0 (η + 1),
      (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0 := fun i0 => by
    have := Set.finsetSum_mem_finsetSum (Finset.Ico i0 (η + 1))
      (fun i => (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0) (fun _ => 0)
      (fun i _ => ⟨0, h0, by simp⟩)
    simpa using this
  have hEO1 : Eset ⊆ O1 := fun e he => by
    rw [hO1, MatExp.particularSolutionOuter]
    exact ⟨0, hsum0 1, e, he, zero_add e⟩
  -- the sets `err` is taken of are bounded
  have hO1b : Bornology.IsBounded O1 :=
    aux_hd_isBounded_of_norm₂_le (MatExp.norm₂_le_of_mem_particularSolutionOuter A hbdd 1 Δt η)
  have hCb : Bornology.IsBounded ((fun x => M.mulVec x)
      '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η) :=
    (mulVecL M).lipschitz.isBounded_image (aux_hd_isBounded_of_norm₂_le
      (MatExp.norm₂_le_of_mem_particularSolutionOuterCorrelated A hbdd 1 Δt η))
  have hRb : Bornology.IsBounded ((fun x => M.mulVec x) '' O1) :=
    (mulVecL M).lipschitz.isBounded_image hO1b
  have hε : (0:ℝ) ≤ MatExp.particularSolutionError A tk U0 Δt η :=
    add_nonneg (err_nonneg _) (err_nonneg _)
  refine hausdorffDist₂_le_of_mem_dist hε ?_ ?_
  -- an exact point: drop its tail, which `err` of `P̂^U_∞(Δt)` bounds
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := sys.inputReach_mem_add_closure_convexHull hconv hclosed hbdd
      hΔt η (hO1b.subset hEO1) hy
    refine ⟨M.mulVec (x + 0), ⟨x + 0, ?_, rfl⟩, ?_⟩
    · rw [MatExp.particularSolutionOuter]
      exact Set.add_mem_add hx hE0
    · have hgap : M.mulVec (x + t) - M.mulVec (x + 0) = M.mulVec t := by
        rw [add_zero, Matrix.mulVec_add, add_sub_cancel_left]
      rw [hgap, MatExp.particularSolutionError]
      have htO1 : t ∈ closure (convexHull ℝ O1) :=
        closure_mono (convexHull_mono hEO1) ht
      exact (norm₂_mulVec_le_err_of_mem_closure_convexHull M hO1b htO1).trans
        (le_add_of_nonneg_left (err_nonneg _))
  -- a point of `P̂^U(Δt)`: the constant input at the same `x₀`
  · rintro _ ⟨ŷ, hŷ, rfl⟩
    obtain ⟨x₀, hx₀, r, hr, rfl⟩ := aux_hd_mem_outer_zero hŷ
    set w := (MatExp.expIntegral A Δt - MatExp.particularCoeff A Δt 0).mulVec x₀ with hw
    -- its gap to `Δtx₀` is eq. (25)'s correlated summand
    have hwmem : w ∈ MatExp.particularSolutionOuterCorrelated A U0 1 Δt η :=
      aux_hd_mem_correlated A hΔt η hx₀
    have hqP : (MatExp.expIntegral A Δt).mulVec x₀ = Δt • x₀ + w := by
      rw [hw, Matrix.sub_mulVec]
      have : (MatExp.particularCoeff A Δt 0).mulVec x₀ = Δt • x₀ := by
        simp only [MatExp.particularCoeff, pow_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
        norm_num
      rw [this]
      abel
    refine ⟨M.mulVec ((MatExp.expIntegral A Δt).mulVec x₀),
      ⟨_, sys.expIntegral_mem_inputReach hΔt.le hx₀, rfl⟩, ?_⟩
    have hgap : M.mulVec (Δt • x₀ + r) - M.mulVec ((MatExp.expIntegral A Δt).mulVec x₀)
        = M.mulVec r - M.mulVec w := by
      rw [hqP, Matrix.mulVec_add, Matrix.mulVec_add]
      abel
    rw [hgap, MatExp.particularSolutionError, add_comm]
    exact (aux_hd_norm₂_sub_le _ _).trans (add_le_add
      (norm₂_le_err_of_mem hRb (Set.mem_image_of_mem _ hr))
      (norm₂_le_err_of_mem hCb (Set.mem_image_of_mem _ hwmem)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
