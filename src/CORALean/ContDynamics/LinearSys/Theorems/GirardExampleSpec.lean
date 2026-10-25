module

public import CORALean.ContDynamics.LinearSys.Theorems.IUnionReachSetExactSubsetLinCombPlusCube
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MemLinCombMtimesIff
public import Mathlib.Analysis.Complex.ExponentialBounds
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The scalar system that breaks [1, Lemma 2]'s printed bound

`x' = 100x + u` with `u ≡ 0` (`µ = 0`), `Z = (1, ⟨1⟩) = [0, 2]`, `r = 1/100`, so `r‖A‖ = 1`. In one
dimension every `p`-norm is the absolute value, so the infinity norm [1] fixes and the induced
matrix norm are `|·|` and `‖A‖ = 100`. Then `sup_{x∈Z} |x| = 2`, `α_r = (e - 2)·2`, `β_r = 0`, and
`P = [1 - e, 2e]`, so `P + □(α_r + β_r)` reaches down to `5 - 3e < 0`, while every reachable state
`e^{100t}z`, `z ∈ [0, 2]`, is at least `0`: the Hausdorff distance is at least `3e - 5 ≈ 3.15`. The
printed bound `r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup |x|)` is `e·(1/2 + 1/100)·2 = 1.02e ≈ 2.77`.
`exists_lt_hausdorffDist_iUnion_reachSetExact` and `exists_lt_hausdorffDist_girardReach` read [1,
Lemma 2] and [1, Thm. 1] off these three facts.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the example's norm, supremum and Hausdorff distance have the stated values

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{tA} z` at the one coordinate, `A = 100`. -/
theorem aux_exp_diag_mulVec (t : ℝ) (z : Vec ℝ 1) :
    (exp (t • (Matrix.diagonal (fun _ : Fin 1 => (100:ℝ)) : Mat ℝ 1 1)) *ᵥ z) 0
      = Real.exp (t * 100) * z 0 := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.mulVec_diagonal]
  simp [Real.exp_eq_exp_ℝ]

/-- The sup norm in dimension one is the absolute value. -/
theorem aux_norm_vec1 (v : Vec ℝ 1) : ‖v‖ = |v 0| := by
  have h : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [h, pi_norm_const, Real.norm_eq_abs]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2] at `x' = 100x + u`, `u = 0`, `Z = [0, 2]`, `r = 1/100`: `‖A‖ = 100`,
`sup_{x∈Z} |x| = 2`, and `d_H(R_[0,r](Z), P + □(α_r + β_r)) ≥ 3e - 5`. -/
theorem LinearSys.girardExample_spec : -- --- CONCL ---
    ‖(Matrix.diagonal fun _ => 100 : Mat ℝ 1 1)‖ = 100
    ∧ IsGreatest ((fun x => ‖x‖) ''
        (⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)).construct) 2
    ∧ 3 * Real.exp 1 - 5 ≤ Metric.hausdorffDist
      (⋃ t ∈ Set.Icc (0:ℝ) (1 / 100),
        (LinearSys.canonical (Matrix.diagonal fun _ => 100) : LinearSys ℝ 1).reachSetExact (S := 𝒵)
          (Set.Icc 0 t) (⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1))
          (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1)) t)
      (((⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)).linComb
          ((⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)).mtimes
            (exp ((1 / 100 : ℝ) • (Matrix.diagonal fun _ => 100 : Mat ℝ 1 1))))).plus
        (Zonotope.cube 1 (2 * (Real.exp 1 - 2)))).construct := by -- --- PROOF ---
  have hnorm : ‖(Matrix.diagonal fun _ => 100 : Mat ℝ 1 1)‖ = 100 := by
    rw [Matrix.linfty_opNorm_diagonal]; simp
  set sys : LinearSys ℝ 1 := LinearSys.canonical (Matrix.diagonal fun _ => 100) with hsys
  set Z : Zonotope (Vec ℝ 1) := ⟨1, fun _ => 1, fun _ _ => 1⟩ with hZ
  set U : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩ with hU
  set E : Mat ℝ 1 1 := exp ((1 / 100 : ℝ) • (Matrix.diagonal fun _ => 100 : Mat ℝ 1 1)) with hE
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hE0 : ∀ v : Vec ℝ 1, (E *ᵥ v) 0 = Real.exp 1 * v 0 := fun v => by
    rw [hE, aux_exp_diag_mulVec]; norm_num
  set R := ⋃ t ∈ Set.Icc (0:ℝ) (1 / 100), sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) Z U t
  set Q := ((Z.linComb (Z.mtimes E)).plus (Zonotope.cube 1 (2 * (Real.exp 1 - 2))))
  -- the point `5 - 3e` of the enclosure
  set p : Vec ℝ 1 := fun _ => 5 - 3 * Real.exp 1
  have hp : p ∈ Q.construct := by
    rw [← Zonotope.plus_exact, Zonotope.cube_exact 1 (by linarith)]
    refine ⟨fun _ => 1 - Real.exp 1, ?_, fun _ => -(2 * (Real.exp 1 - 2)), ?_, ?_⟩
    · refine Zonotope.mem_linComb_mtimes_iff.mpr ⟨fun _ => -1, fun _ => 1, 1, fun _ => by simp,
        fun _ => by simp, by simp, ?_⟩
      funext i
      rw [Subsingleton.elim i 0]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hE0]
      simp [hZ]
      ring
    · rw [mem_closedBall_zero_iff, aux_norm_vec1, abs_neg, abs_of_nonneg (by linarith)]
    · funext i; simp [p]; ring
  have hz0 : ∀ β : Fin Z.h → ℝ, (Z.c + ∑ j, β j • Z.G j) 0 = 1 + β 0 := fun β => by
    show (((fun _ => (1:ℝ)) : Vec ℝ 1) + ∑ j : Fin 1, β j • ((fun _ => (1:ℝ)) : Vec ℝ 1)) 0
      = 1 + β 0
    simp
  -- every reachable state stays at or above `0`, the input set being `{0}`
  have hU0 : ∀ u ∈ U.construct, u = 0 := by
    rintro u ⟨β, -, rfl⟩
    simp [hU]
  have hU0' : (0 : Vec ℝ 1) ∈ U.construct := ⟨Fin.elim0, fun j => j.elim0, by simp [hU]⟩
  have hRnn : ∀ y ∈ R, 0 ≤ y 0 := by
    intro y hy
    obtain ⟨t, ⟨ht0, -⟩, hyt⟩ := Set.mem_iUnion₂.mp hy
    rw [sys.reachSetExact_eq (S := 𝒵) Z U ht0 (Zonotope.isBounded_construct U)] at hyt
    obtain ⟨_, ⟨z, ⟨β, hβ, rfl⟩, rfl⟩, v, ⟨u, hu, -, rfl⟩, rfl⟩ := hyt
    -- the input integral vanishes, the input being `0` throughout
    have hv : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : Vec ℝ 1)) (fun s hs => ?_)]
      · simp
      · rw [Set.uIcc_of_le ht0] at hs
        simp [hU0 _ (hu s hs)]
    show 0 ≤ ((exp (t • toRealMat sys.A)).mulVecLin (Z.c + ∑ j, β j • Z.G j)
      + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) 0
    rw [hv, add_zero, Matrix.mulVecLin_apply]
    -- what is left is `e^{100t} z` at `z ≥ 0`
    show 0 ≤ (exp (t • (Matrix.diagonal fun _ => (100:ℝ) : Mat ℝ 1 1)) *ᵥ _) 0
    rw [aux_exp_diag_mulVec]
    refine mul_nonneg (Real.exp_nonneg _) ?_
    rw [hz0]
    linarith [(abs_le.mp (hβ 0)).1]
  -- `R` is nonempty and bounded, so the Hausdorff distance is finite
  have hRne : R.Nonempty := by
    refine ⟨(exp ((0:ℝ) • toRealMat sys.A)).mulVecLin Z.c + 0,
      Set.mem_iUnion₂.mpr ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩⟩
    rw [sys.reachSetExact_eq (S := 𝒵) Z U le_rfl (Zonotope.isBounded_construct U)]
    have h0 := sys.expIntegral_mem_inputReach (S := 𝒵) (le_refl (0:ℝ)) hU0'
    rw [Matrix.mulVec_zero] at h0
    exact ⟨_, ⟨Z.c, Zonotope.center_mem_construct Z, rfl⟩, 0, h0, rfl⟩
  -- bounded: inside the enclosure of Lemma 2
  have hRb : Bornology.IsBounded R := by
    have hs : ∀ z ∈ Z.construct, ‖z‖ ≤ 2 := by
      rintro _ ⟨β, hβ, rfl⟩
      rw [aux_norm_vec1]
      have := abs_le.mp (hβ 0)
      rw [hz0, abs_le]; constructor <;> linarith
    have hUc : U.construct = Metric.closedBall 0 0 := by
      rw [Metric.closedBall_zero]
      ext u; constructor
      · exact hU0 u
      · rintro rfl; exact hU0'
    exact (Zonotope.isBounded_construct _).subset
      (sys.iUnion_reachSetExact_subset_linComb_plus_cube Z U (by
        show 0 < ‖(Matrix.diagonal fun _ => (100:ℝ) : Mat ℝ 1 1)‖
        rw [hnorm]; norm_num) (by norm_num) le_rfl hUc hs)
  -- the distance from `5 - 3e` to anything at or above `0`
  have hinf : 3 * Real.exp 1 - 5 ≤ Metric.infDist p R := by
    refine (Metric.le_infDist hRne).mpr fun y hy => ?_
    rw [dist_eq_norm, aux_norm_vec1]
    have := hRnn y hy
    simp only [Pi.sub_apply, p]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hfin : Metric.hausdorffEDist Q.construct R ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨p, hp⟩ hRne
      (Zonotope.isBounded_construct Q) hRb
  -- the three facts: `‖A‖`, `sup |x| = 2`, the distance
  refine ⟨hnorm, ⟨⟨fun _ => 2, ⟨fun _ => 1, fun _ => by simp, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · funext i; show (2:ℝ) = 1 + ∑ j : Fin 1, (1:ℝ) * 1; simp; norm_num
  · show ‖(fun _ => (2:ℝ) : Vec ℝ 1)‖ = 2
    rw [aux_norm_vec1]; norm_num
  · rintro _ ⟨z, ⟨β, hβ, rfl⟩, rfl⟩
    have := abs_le.mp (hβ 0)
    show ‖Z.c + ∑ j, β j • Z.G j‖ ≤ 2
    rw [aux_norm_vec1, hz0, abs_le]; constructor <;> linarith
  · rw [Metric.hausdorffDist_comm]
    exact hinf.trans (Metric.infDist_le_hausdorffDist_of_mem hp hfin)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
