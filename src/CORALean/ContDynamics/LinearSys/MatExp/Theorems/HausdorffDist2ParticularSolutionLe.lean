import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsParticularTailEntryLe
import CORALean.Global.EuclideanHausdorffDist

/-!
# [1, Prop. 11]: the error of eq. (20)'s particular solution, propagated by `e^{At_k}`

`P^U(Δt)` is squeezed between [1]'s own inner-approximation `qP^U(Δt) = (∫₀^{Δt}e^{A(Δt-θ)}dθ)U0`
— constant inputs, `MatExp.expIntegral` — and eq. (20)'s `bPU(Δt)`, and those two inclusions are
all [1]'s proof uses of it, so they are what this theorem asks for. `Real.MatExp.expIntegral_mulVec`
and `LinearSys.expIntegral_mem_inputReach` discharge the first for the exact `P^U(Δt)`; the second
is eq. (20)'s soundness, which [1] cites to Althoff's thesis rather than proving.

The witness is more direct than [1]'s own two-step triangle inequality: for `Δtx₀ ⊕ r ∈ bPU(Δt)`
the nearby exact point is `qP^U`'s own `(∫₀^{Δt}e^{A(Δt-θ)}dθ)x₀` at the *same* `x₀`, whose gap
`(Σ_{i≥1}Ãᵢ)x₀` is eq. (25)'s *correlated* summand and `r` its decorrelated one. The tail past `η`
is `MatExp.abs_particularTail_entry_le`, which is where `E(Δt,η)Δt` enters.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A uniform `‖·‖₂` bound is boundedness, the supremum norm being the smaller of the two. -/
theorem aux_isBounded_of_forall_norm₂_le {S : Set (Vec ℝ n)} {r : ℝ}
    (h : ∀ y ∈ S, ‖y‖₂ ≤ r) : Bornology.IsBounded S := by
  refine isBounded_iff_forall_norm_le.mpr ⟨max r 0, fun y hy => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_max_right r 0)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact ((abs_le_norm₂ y i).trans (h y hy)).trans (le_max_left r 0)

/-- And a matrix image of such a set is bounded too. -/
theorem aux_isBounded_mulVec_image {S : Set (Vec ℝ n)} {r : ℝ} (M : Mat ℝ n n)
    (h : ∀ y ∈ S, ‖y‖₂ ≤ r) : Bornology.IsBounded ((fun x => M.mulVec x) '' S) := by
  refine aux_isBounded_of_forall_norm₂_le (r := (∑ i, ‖(fun j => M i j)‖₂) * max r 0) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (norm₂_mulVec_le M y).trans (mul_le_mul_of_nonneg_left ((h y hy).trans (le_max_left r 0))
    (Finset.sum_nonneg fun i _ => norm₂_nonneg _))

/-- The triangle inequality on a difference, `norm₂_add_le` through `(-1) •`. -/
theorem aux_norm₂_sub_le (x y : Vec ℝ n) : ‖x - y‖₂ ≤ ‖x‖₂ + ‖y‖₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ y]
  refine (norm₂_add_le _ _).trans_eq ?_
  rw [norm₂_smul]
  norm_num

/-- Eq. (20)'s order-`0` block split off: `bPU(Δt) = ΔtU0 ⊕ bPU_∞(Δt)`, eq. (27). -/
theorem aux_mem_particularSolutionOuter_zero {A : Mat ℝ n n} {U0 : Set (Vec ℝ n)} {Δt : ℝ}
    {η : ℕ} {y : Vec ℝ n} (hy : y ∈ MatExp.particularSolutionOuter A U0 0 Δt η) :
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

/-- The gap between `qP^U`'s point at `x₀` and eq. (27)'s `Δtx₀` is eq. (25)'s correlated summand:
orders `1` to `η` exactly, and everything past `η` inside `E(Δt,η)Δt`. -/
theorem aux_mem_particularSolutionOuterCorrelated (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)} {Δt : ℝ}
    (hΔt : 0 < Δt) (η : ℕ) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ U0) :
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


-- =======================================  MAIN THEOREM  ======================================= --

-- a dozen `Set`-valued `have`s over `Vec ℝ n`, each re-solving the local matrix instances
set_option maxHeartbeats 400000 in
/-- [1, Prop. 11]: eq. (25) bounds `d_H(e^{At_k}P^U(Δt), e^{At_k}bPU(Δt))` for every `P` between
[1]'s constant-input inner-approximation and eq. (20)'s outer one. -/
theorem MatExp.hausdorffDist₂_particularSolution_le (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    {P : Set (Vec ℝ n)}
    (hinner : (fun c => (MatExp.expIntegral A Δt).mulVec c) '' U0 ⊆ P)
    (houter : P ⊆ MatExp.particularSolutionOuter A U0 0 Δt η) :
    hausdorffDist₂ ((fun x => (exp (tk • A)).mulVec x) '' P)
        ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 0 Δt η)
      ≤ MatExp.particularSolutionError A tk U0 Δt η := by -- --- PROOF ---
  have hCb : Bornology.IsBounded ((fun x => (exp (tk • A)).mulVec x)
      '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η) :=
    aux_isBounded_mulVec_image _
      (MatExp.norm₂_le_of_mem_particularSolutionOuterCorrelated A hU0 1 Δt η)
  have hRb : Bornology.IsBounded ((fun x => (exp (tk • A)).mulVec x)
      '' MatExp.particularSolutionOuter A U0 1 Δt η) :=
    aux_isBounded_mulVec_image _ (MatExp.norm₂_le_of_mem_particularSolutionOuter A hU0 1 Δt η)
  have hε : (0:ℝ) ≤ MatExp.particularSolutionError A tk U0 Δt η :=
    add_nonneg (err_nonneg _) (err_nonneg _)
  refine hausdorffDist₂_le_of_mem_dist hε ?_ ?_
  -- one side is free: `P` sits inside its own outer-approximation
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(exp (tk • A)).mulVec y, ⟨y, houter hy, rfl⟩, by rw [sub_self, norm₂_zero]; exact hε⟩
  -- the other side: eq. (27)'s `Δtx₀` fixes which exact point of `qP^U` to compare against
  · rintro _ ⟨ŷ, hŷ, rfl⟩
    obtain ⟨x₀, hx₀, r, hr, rfl⟩ := aux_mem_particularSolutionOuter_zero hŷ
    set w := (MatExp.expIntegral A Δt - MatExp.particularCoeff A Δt 0).mulVec x₀ with hw
    have hwmem : w ∈ MatExp.particularSolutionOuterCorrelated A U0 1 Δt η :=
      aux_mem_particularSolutionOuterCorrelated A hΔt η hx₀
    have hqP : (MatExp.expIntegral A Δt).mulVec x₀ = Δt • x₀ + w := by
      rw [hw, Matrix.sub_mulVec]
      have : (MatExp.particularCoeff A Δt 0).mulVec x₀ = Δt • x₀ := by
        simp only [MatExp.particularCoeff, pow_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
        norm_num
      rw [this]
      abel
    -- what is left after `Δtx₀` cancels is `r` against `w`, one error summand each
    refine ⟨(exp (tk • A)).mulVec ((MatExp.expIntegral A Δt).mulVec x₀),
      ⟨_, hinner ⟨x₀, hx₀, rfl⟩, rfl⟩, ?_⟩
    have hgap : (exp (tk • A)).mulVec (Δt • x₀ + r)
        - (exp (tk • A)).mulVec ((MatExp.expIntegral A Δt).mulVec x₀)
        = (exp (tk • A)).mulVec r - (exp (tk • A)).mulVec w := by
      rw [hqP, Matrix.mulVec_add, Matrix.mulVec_add]
      abel
    show ‖(exp (tk • A)).mulVec (Δt • x₀ + r)
      - (exp (tk • A)).mulVec ((MatExp.expIntegral A Δt).mulVec x₀)‖₂ ≤ _
    rw [hgap, MatExp.particularSolutionError, add_comm]
    exact (aux_norm₂_sub_le _ _).trans (add_le_add
      (norm₂_le_err_of_mem hRb (Set.mem_image_of_mem _ hr))
      (norm₂_le_err_of_mem hCb (Set.mem_image_of_mem _ hwmem)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
