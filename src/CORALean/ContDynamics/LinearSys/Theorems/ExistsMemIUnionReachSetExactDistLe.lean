module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpMulVecSubInterpolateLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubOneSubLeSqMulExp
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.Cube
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.CubeExact
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.MemLinCombMtimesIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# Every point of the first enclosure is near a reachable one

The half of [1, Lemma 2]'s convergence claim that is not the enclosure itself: a point `q = p + w`
of `P + □(α_r + β_r)` is within `r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)` of `R_[0,r](Z)`. As in
the printed proof, `p` splits as `(z + e^{rA}z)/2 + (I - e^{rA})z'/2` with `z ∈ Z` and
`‖z'‖ ≤ sup ‖x‖`; the reachable point is `e^{(r/2)A}z`, the input held at `0`. The printed proof
bounds `2α_r` by `e^{r‖A‖} r² sup ‖x‖`, which is false whenever `‖A‖ > 1` and `r` is small: `α_r` is
of order `(r‖A‖)²`, not `r²`. What `e^x - 1 - x ≤ x²e^x/2` gives is
`2α_r ≤ (r‖A‖)² e^{r‖A‖} sup ‖x‖`, so the factor printed as `(1/2 + r)` is `(1/2 + r‖A‖)` here
(`exists_lt_hausdorffDist_iUnion_reachSetExact` shows the printed one fails).

## Inputs
* `sys` – linear system
* `Z` – initial zonotope
* `U` – input zonotope
* `μ` – input bound
* `r` – step length
* `s` – norm bound of the initial zonotope
* `q` – point of the first enclosure

## Hypotheses
* `hA` – matrix norm positive
* `hr` – step length positive
* `hμ` – input bound nonnegative
* `hU` – input set is the ball of that radius
* `hs` – norm bound holds on the initial zonotope
* `hq` – point lies in the first enclosure

## Conclusion
* the point is within the corrected distance of a reachable point

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^x - 1 ≤ x e^x`: `1 - x ≤ e^{-x}`, multiplied by `e^x`. -/
theorem aux_exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos x]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], convergence, the direction from the enclosure: every point of
`P + □(α_r + β_r)` is within `r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)` of `R_[0,r](Z)`. -/
theorem LinearSys.exists_mem_iUnion_reachSetExact_dist_le (sys : LinearSys 𝕋 n)
    (Z U : Zonotope (Vec ℝ n)) {μ r s : ℝ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 < r)
    (hμ : 0 ≤ μ) (hU : U.construct = Metric.closedBall 0 μ)
    (hs : ∀ z ∈ Z.construct, ‖z‖ ≤ s) {q : Vec ℝ n}
    (hq : q ∈ ((Z.linComb (Z.mtimes (exp (r • toRealMat sys.A)))).plus
          (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖) * s
            + (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ))).construct)
    : -- --- CONCL ---
    ∃ y ∈ ⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) Z U t,
      dist q y ≤ r * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
        * (μ / ‖toRealMat sys.A‖ + (1 / 2 + r * ‖toRealMat sys.A‖) * s) := by -- --- PROOF ---
  set A := toRealMat sys.A
  set a := ‖A‖
  set x := r * a with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hr.le hA.le
  have hex := Real.add_one_le_exp x
  have hα0 : 0 ≤ Real.exp x - 1 - x := by linarith
  have hβ0 : 0 ≤ (Real.exp x - 1) / a * μ := mul_nonneg (div_nonneg (by linarith) hA.le) hμ
  have hs0 : 0 ≤ s := (norm_nonneg Z.c).trans (hs _ (Zonotope.center_mem_construct Z))
  -- `q = p + w`, `p` split at its coefficients
  rw [← Zonotope.plus_exact, Zonotope.cube_exact n (add_nonneg (mul_nonneg hα0 hs0) hβ0)] at hq
  obtain ⟨p, hp, w, hw, rfl⟩ := hq
  obtain ⟨β, γ, m, hβ, hγ, hm, hpeq⟩ := Zonotope.mem_linComb_mtimes_iff.mp hp
  set z := Z.c + ∑ j, β j • Z.G j with hzdef
  set z' := m • Z.c + ∑ j, γ j • Z.G j with hz'def
  have hz : z ∈ Z.construct := ⟨β, hβ, rfl⟩
  -- `z'` is a convex combination of `c + Σγg` and `-(c - Σγg)`, both of norm at most `s`
  have hz' : ‖z'‖ ≤ s := by
    have h1 : Z.c + ∑ j, γ j • Z.G j ∈ Z.construct := ⟨γ, hγ, rfl⟩
    have h2 : Z.c + ∑ j, (-γ j) • Z.G j ∈ Z.construct := ⟨fun j => -γ j, fun j => by
      rw [abs_neg]; exact hγ j, rfl⟩
    have hm1 := (abs_le.mp hm)
    have heq : z' = ((1 + m) / 2) • (Z.c + ∑ j, γ j • Z.G j)
        - ((1 - m) / 2) • (Z.c + ∑ j, (-γ j) • Z.G j) := by
      simp only [hz'def, neg_smul, Finset.sum_neg_distrib]; module
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ (1 + m) / 2), abs_of_nonneg (by linarith : 0 ≤ (1 - m) / 2)]
    nlinarith [hs _ h1, hs _ h2]
  -- the reachable companion: `e^{(r/2)A}z`, the input held at `0`
  have hr2 : r / 2 ∈ Set.Icc (0:ℝ) r := ⟨by linarith, by linarith⟩
  have h0U : (0 : Vec ℝ n) ∈ construct U := by
    show (0 : Vec ℝ n) ∈ U.construct
    rw [hU]; exact Metric.mem_closedBall_self hμ
  have h0 : (0 : Vec ℝ n) ∈ sys.inputReach (S := 𝒵) U (r / 2) := by
    have := sys.expIntegral_mem_inputReach (S := 𝒵) hr2.1 h0U
    rwa [Matrix.mulVec_zero] at this
  refine ⟨exp ((r / 2) • A) *ᵥ z, Set.mem_iUnion₂.mpr ⟨r / 2, hr2, ?_⟩, ?_⟩
  · rw [sys.reachSetExact_eq (S := 𝒵) Z U hr2.1 (Zonotope.isBounded_construct U)]
    exact ⟨_, ⟨z, hz, rfl⟩, 0, h0, add_zero _⟩
  -- three pieces: the bloating `w`, the midpoint against the flow, and `(I - e^{rA})z'/2`
  have hint := MatExp.norm_exp_mulVec_sub_interpolate_le A hr2.1 hr2.2 z
  have hhalf : r / 2 / r = (2:ℝ)⁻¹ := by field_simp
  rw [hhalf] at hint
  have hE := norm_exp_smul_sub_one_le A hr.le
  have hdiff : ‖z' - exp (r • A) *ᵥ z'‖ ≤ x * Real.exp x * s := by
    have : z' - exp (r • A) *ᵥ z' = -((exp (r • A) - 1) *ᵥ z') := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [this, norm_neg]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul hE hz' (norm_nonneg _) (by positivity))
-- the distance, regrouped into the three pieces
  have heq : p + w - exp ((r / 2) • A) *ᵥ z
      = w - (exp ((r / 2) • A) *ᵥ z - z - (2:ℝ)⁻¹ • (exp (r • A) *ᵥ z - z))
        + (2:ℝ)⁻¹ • (z' - exp (r • A) *ᵥ z') := by
    rw [hpeq]; module
  rw [dist_eq_norm, heq]
  have hwle : ‖w‖ ≤ (Real.exp x - 1 - x) * s + (Real.exp x - 1) / a * μ :=
    mem_closedBall_zero_iff.mp hw
  have hintle : ‖exp ((r / 2) • A) *ᵥ z - z - (2:ℝ)⁻¹ • (exp (r • A) *ᵥ z - z)‖
      ≤ (Real.exp x - 1 - x) * s :=
    hint.trans (mul_le_mul_of_nonneg_left (hs z hz) hα0)
  have hhalfle : ‖(2:ℝ)⁻¹ • (z' - exp (r • A) *ᵥ z')‖ ≤ (2:ℝ)⁻¹ * (x * Real.exp x * s) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
    exact mul_le_mul_of_nonneg_left hdiff (by norm_num)
  -- and the closed form: `e^x - 1 - x ≤ x²e^x/2`, `e^x - 1 ≤ xe^x`
  have hq2 := exp_sub_one_sub_le_sq_mul_exp hx0
  have hq1 := aux_exp_sub_one_le_mul_exp x
  have hβle : (Real.exp x - 1) / a * μ ≤ x * Real.exp x * (μ / a) := by
    rw [div_mul_eq_mul_div, mul_div_assoc']
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq1 hμ) hA.le
  have hαle : (Real.exp x - 1 - x) * s ≤ x ^ 2 / 2 * Real.exp x * s :=
    mul_le_mul_of_nonneg_right hq2 hs0
  calc ‖w - (exp ((r / 2) • A) *ᵥ z - z - (2:ℝ)⁻¹ • (exp (r • A) *ᵥ z - z))
        + (2:ℝ)⁻¹ • (z' - exp (r • A) *ᵥ z')‖
      ≤ ‖w‖ + ‖exp ((r / 2) • A) *ᵥ z - z - (2:ℝ)⁻¹ • (exp (r • A) *ᵥ z - z)‖
        + ‖(2:ℝ)⁻¹ • (z' - exp (r • A) *ᵥ z')‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ x * Real.exp x * (μ / a + (1 / 2 + x) * s) := by
        have : x * Real.exp x * (μ / a + (1 / 2 + x) * s) = x * Real.exp x * (μ / a)
            + (2:ℝ)⁻¹ * (x * Real.exp x * s) + 2 * (x ^ 2 / 2 * Real.exp x * s) := by ring
        rw [this]
        linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
