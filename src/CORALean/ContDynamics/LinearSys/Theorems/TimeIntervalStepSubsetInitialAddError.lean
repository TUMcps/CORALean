module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrectionMatrixLe
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.PairDiff
public import CORALean.ContSet.Zonotope.Real.Operations.PairSum
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# What the step encloses beyond the initial set it starts from

`timeIntervalStep_outer` run backwards, and sharper than
`timeIntervalStep_subset_reach_add_error`: the exact point the enclosure is
measured against is the state at `t = 0`, so the set on the right is `X₀`
itself — a zonotope, hence convex and compact — rather than the union over the
step, which is a union of images and need not be convex at all. That is what an
inner approximation of the step needs, and what the union cannot give.

The hull gap is real and it is the larger term. `linComb X₀ (e^{Ar}X₀)` reaches
outside every state the flow visits over the step, and a zonotope's `linComb` is
itself wider than the hull of its two operands. What that costs is
`‖e^{Ar} - I‖` against the initial set's `ℓ¹` reach — *first* order in the step,
where the correction matrix meant to account for the interpolation is second. So
the correction does not pay for the hull, and no truncation order does either:
`ε` reaches only the smaller of the two terms. What [1] tunes reaches the
correction and not the hull.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a zonotope, and its generators, against its `ℓ¹` reach. -/
theorem aux_norm_add_sum_le_absBound_sum (Z : Zonotope (Vec ℝ n)) :
    ‖Z.c‖ + ∑ j, ‖Z.G j‖ ≤ ∑ i, Z.absBound i := by -- --- PROOF ---
  have hpi : ∀ v : Vec ℝ n, ‖v‖ ≤ ∑ i, |v i| := by
    intro v
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (v k)) (Finset.mem_univ i)
  have hG : ∑ j, ‖Z.G j‖ ≤ ∑ j, ∑ i, |Z.G j i| := Finset.sum_le_sum fun j _ => hpi (Z.G j)
  have hswap : ∑ j, ∑ i, |Z.G j i| = ∑ i, ∑ j, |Z.G j i| := Finset.sum_comm
  -- the two blocks of `absBound`, read down the coordinates rather than across
  have habs : ∑ i, Z.absBound i = ∑ i, |Z.c i| + ∑ i, ∑ j, |Z.G j i| := by
    simp only [Zonotope.absBound]
    rw [Finset.sum_add_distrib]
  have hc := hpi Z.c
  rw [habs, ← hswap]
  linarith

theorem aux_sum_univ_linCombPaired {h : ℕ} {c₁ c₂ : Vec ℝ n} {G₁ G₂ : Fin h → Vec ℝ n}
    (f : Fin (h + h + 1) → Vec ℝ n) :
    ∑ j : Fin (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).h, f j
      = ∑ j : Fin (h + h), f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd (h + h) j) :=
  Fin.sum_univ_add f

theorem aux_linComb_paired_subset {h : ℕ} (c₁ c₂ : Vec ℝ n)
    (G₁ G₂ : Fin h → Vec ℝ n) : -- --- STMT ---
    (Zonotope.linComb ⟨h, c₁, G₁⟩ ⟨h, c₂, G₂⟩).construct
      ⊆ (Zonotope.mk h c₁ G₁).construct
        + Metric.closedBall (0 : Vec ℝ n)
            (‖c₁ - c₂‖ + ∑ j, ‖G₁ j - G₂ j‖) := by -- --- PROOF ---
  have hgS : ∀ i : Fin h,
      (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).G
          (Fin.castAdd 1 (Fin.castAdd h i)) = (2:ℝ)⁻¹ • (G₁ i + G₂ i) := by
    intro i
    show Fin.append (Fin.append (Zonotope.pairSum G₁ G₂) (Zonotope.pairDiff G₁ G₂))
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (c₁ - c₂)) (Fin.castAdd 1 (Fin.castAdd h i)) = _
    rw [Fin.append_left, Fin.append_left, Zonotope.pairSum, dif_pos i.isLt]
  -- the second block of the pairing, the half-difference of the two generators
  have hgD : ∀ i : Fin h,
      (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).G
          (Fin.castAdd 1 (Fin.natAdd h i)) = (2:ℝ)⁻¹ • (G₁ i - G₂ i) := by
    intro i
    show Fin.append (Fin.append (Zonotope.pairSum G₁ G₂) (Zonotope.pairDiff G₁ G₂))
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (c₁ - c₂)) (Fin.castAdd 1 (Fin.natAdd h i)) = _
    rw [Fin.append_left, Fin.append_right, Zonotope.pairDiff, dif_pos i.isLt]
  -- and the fresh generator, which is what lets the combination slide
  have hgC : ∀ i : Fin 1,
      (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).G
          (Fin.natAdd (h + h) i) = (2:ℝ)⁻¹ • (c₁ - c₂) := by
    intro i
    show Fin.append (Fin.append (Zonotope.pairSum G₁ G₂) (Zonotope.pairDiff G₁ G₂))
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (c₁ - c₂)) (Fin.natAdd (h + h) i) = _
    rw [Fin.append_right]
  -- the coefficients, one family per block
  rintro y ⟨β, hβ, rfl⟩
  set α : Fin h → ℝ := fun j => β (Fin.castAdd 1 (Fin.castAdd h j)) with hα
  set γ : Fin h → ℝ := fun j => β (Fin.castAdd 1 (Fin.natAdd h j)) with hγ
  set δ : ℝ := β (Fin.natAdd (h + h) 0) with hδ
  have hαb : ∀ j, |α j| ≤ 1 := fun j => hβ _
  have hγb : ∀ j, |γ j| ≤ 1 := fun j => hβ _
  have hδb : |δ| ≤ 1 := hβ _
  have hsplit : ∑ j, β j • (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).G j
      = (∑ j : Fin h, α j • ((2:ℝ)⁻¹ • (G₁ j + G₂ j))
          + ∑ j : Fin h, γ j • ((2:ℝ)⁻¹ • (G₁ j - G₂ j)))
        + δ • ((2:ℝ)⁻¹ • (c₁ - c₂)) := by
    rw [aux_sum_univ_linCombPaired, Fin.sum_univ_add]
    simp only [hgS, hgD, hgC, Fin.sum_univ_one, hα, hγ, hδ]
  have hc : (Zonotope.linComb (⟨h, c₁, G₁⟩ : Zonotope (Vec ℝ n)) ⟨h, c₂, G₂⟩).c
      = (2:ℝ)⁻¹ • (c₁ + c₂) := rfl
  -- the witness keeps the first block's coefficients and drops everything else
  rw [hc, hsplit]
  refine ⟨c₁ + ∑ j, α j • G₁ j, ⟨α, hαb, rfl⟩,
    ((1 - δ) * (2:ℝ)⁻¹) • (c₂ - c₁)
      + ∑ j, ((γ j - α j) * (2:ℝ)⁻¹) • (G₁ j - G₂ j), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, ← norm_neg (c₂ - c₁), neg_sub]
      -- the two coefficients of the center are free, so their spread is at most two
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      rw [abs_le] at hδb
      have h2 : |1 - δ| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      have hab := abs_le.mp (hαb j)
      have hgb := abs_le.mp (hγb j)
      have h2 : |γ j - α j| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
  · -- and the two blocks recombine into the witness and the difference
    have hterm : ∀ j : Fin h,
        α j • ((2:ℝ)⁻¹ • (G₁ j + G₂ j)) + γ j • ((2:ℝ)⁻¹ • (G₁ j - G₂ j))
          = α j • G₁ j + ((γ j - α j) * (2:ℝ)⁻¹) • (G₁ j - G₂ j) := fun j => by module
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => hterm j),
      Finset.sum_add_distrib]
    module


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reverse of `timeIntervalStep_outer`, against the set the step starts
from: what it computes stays inside `X₀` widened by `timeIntervalStepError`. -/
theorem LinearSys.timeIntervalStep_subset_initial_add_error (sys : LinearSys 𝕋 n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ : Zonotope (Vec ℝ n)) : -- --- STMT ---
    (sys.timeIntervalStep (S := 𝒵) r η X₀).construct
      ⊆ X₀.construct
        + Metric.closedBall (0 : Vec ℝ n)
            (sys.timeIntervalStepError r η X₀) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set M := exp (r • A) with hM
  set B := ∑ j, X₀.absBound j with hB
  set ρF := Real.exp (r * ‖A‖) - 1 - r * ‖A‖ + MatExp.expRemainderBound (r • A) η with hρF
  have hB0 : (0:ℝ) ≤ B := Finset.sum_nonneg fun j _ => by
    rw [Zonotope.absBound]
    positivity
  have hρF0 : (0:ℝ) ≤ ρF := by
    rw [hρF, MatExp.expRemainderBound]
    have h1 : (0:ℝ) < 1 - ‖r • A‖ / ((η : ℝ) + 2) := by linarith
    have h2 : r * ‖A‖ + 1 ≤ Real.exp (r * ‖A‖) := Real.add_one_le_exp _
    have h3 : (0:ℝ) ≤ (‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
        * (1 - ‖r • A‖ / ((η : ℝ) + 2))⁻¹ := by positivity
    linarith
  -- what the hull between the set and its image reaches past the set itself
  have hhull : (Zonotope.linComb X₀ (Zonotope.mtimes M X₀)).construct
      ⊆ X₀.construct + Metric.closedBall (0 : Vec ℝ n)
          (‖X₀.c - M *ᵥ X₀.c‖ + ∑ j, ‖X₀.G j - M *ᵥ X₀.G j‖) :=
    aux_linComb_paired_subset X₀.c (M *ᵥ X₀.c) X₀.G (fun j => M *ᵥ X₀.G j)
  have hdiff : ‖X₀.c - M *ᵥ X₀.c‖ + ∑ j, ‖X₀.G j - M *ᵥ X₀.G j‖ ≤ ‖M - 1‖ * B := by
    have hv : ∀ v : Vec ℝ n, ‖v - M *ᵥ v‖ ≤ ‖M - 1‖ * ‖v‖ := by
      intro v
      have heq : v - M *ᵥ v = -((M - 1) *ᵥ v) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [heq, norm_neg]
      exact Matrix.linfty_opNorm_mulVec _ _
    calc ‖X₀.c - M *ᵥ X₀.c‖ + ∑ j, ‖X₀.G j - M *ᵥ X₀.G j‖
        ≤ ‖M - 1‖ * ‖X₀.c‖ + ∑ j, ‖M - 1‖ * ‖X₀.G j‖ :=
          add_le_add (hv _) (Finset.sum_le_sum fun j _ => hv _)
      _ = ‖M - 1‖ * (‖X₀.c‖ + ∑ j, ‖X₀.G j‖) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ ‖M - 1‖ * B :=
          mul_le_mul_of_nonneg_left (aux_norm_add_sum_le_absBound_sum X₀) (norm_nonneg _)
  -- and what the correction matrix adds, both of its endpoints bounded at once
  have hbox : ∀ q ∈ (Zonotope.mtimesIntervalMat (MatExp.correctionMatrix A r η) X₀).construct,
      ‖q‖ ≤ (ρF + ρF) * B := by
    intro q hq
    have hcen : ∀ i j, |(MatExp.correctionMatrix A r η).center i j| ≤ ρF := by
      intro i j
      obtain ⟨hinf, hsup⟩ := MatExp.abs_correctionMatrix_le A hr.le hε i j
      have hval : (MatExp.correctionMatrix A r η).center i j
          = (2:ℝ)⁻¹ * ((MatExp.correctionMatrix A r η).inf i j
            + (MatExp.correctionMatrix A r η).sup i j) := rfl
      -- the center is the midpoint, so it is under whichever endpoint is larger
      have habs := abs_add_le ((MatExp.correctionMatrix A r η).inf i j)
        ((MatExp.correctionMatrix A r η).sup i j)
      rw [hval, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      linarith
    -- and the radius is the half-width, which the same two endpoints bound
    have hrad : ∀ i j, |(MatExp.correctionMatrix A r η).radius i j| ≤ ρF := by
      intro i j
      obtain ⟨hinf, hsup⟩ := MatExp.abs_correctionMatrix_le A hr.le hε i j
      have hval : (MatExp.correctionMatrix A r η).radius i j
          = (2:ℝ)⁻¹ * ((MatExp.correctionMatrix A r η).sup i j
            - (MatExp.correctionMatrix A r η).inf i j) := rfl
      have habs := abs_sub ((MatExp.correctionMatrix A r η).sup i j)
        ((MatExp.correctionMatrix A r η).inf i j)
      rw [hval, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      linarith
    have hmem := Zonotope.mtimesIntervalMat_subset_closedBall _ X₀ hρF0 hρF0 hcen hrad hq
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  -- the step splits exactly into the hull and the correction
  intro y hy
  rw [show sys.timeIntervalStep (S := 𝒵) r η X₀
      = (Zonotope.linComb X₀ (Zonotope.mtimes M X₀)).plus
          (Zonotope.mtimesIntervalMat (MatExp.correctionMatrix A r η) X₀) from rfl,
    ← Zonotope.plus_exact] at hy
  obtain ⟨p, hp, q, hq, rfl⟩ := hy
  obtain ⟨x, hx, d, hd, rfl⟩ := hhull hp
  rw [Metric.mem_closedBall, dist_zero_right] at hd
  -- the exact point is the state at the start of the step, before the flow moves
  refine ⟨x, hx, d + q, ?_, (add_assoc x d q).symm⟩
  · rw [Metric.mem_closedBall, dist_zero_right, LinearSys.timeIntervalStepError,
      ← hA, ← hM, ← hB, ← hρF]
    have hfinal : ‖M - 1‖ * B + (ρF + ρF) * B = B * (‖M - 1‖ + 2 * ρF) := by ring
    refine ((norm_add_le _ _).trans (add_le_add (hd.trans hdiff) (hbox q hq))).trans ?_
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
