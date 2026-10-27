module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetExistsForallExact
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReach
public import CORALean.ContDynamics.LinearSys.Theorems.PerturbedSuperposition
public import CORALean.Global.EuclideanGenOpNorm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `Thm. 2` of TAC 2026 is false: (54) is not inside (53)

[1, Thm. 2] claims (54) is inside (53). Refuted for `ẋ = (x₂, x₃, 0)`, `U = W = {0}`, `τ = [0, 1/8]`
in one step, `η ≥ 2` and the box `X_end`: `|x₁| ≤ 1`, `|x₂| ≤ 1/4`, `|x₃ - 256| ≤ 1/4`. Then (54)
is `e^{-AΔt}conv(P₁, P₂)`, [1, Alg. 3]'s lines 3-5 as `LinearSys.maxBackReach` computes them. It
holds `(7/4, -16, 256)`, the image of the midpoint of `(3/4, 0, 256) ∈ P₁` and its step in `P₂`; the
run from it keeps its first coordinate at `5/4 + 128(t - 1/16)² > 1`. The lines are spelled out,
with the exact `box(X_end)` where `LinearSys.maxBackReach` takes the oracle's answer.

## Inputs
* `η` – Taylor order

## Hypotheses
* `hη` – Taylor order at least two

## Conclusion
* a point of (54) from which no run meets the target set in `τ`

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace Set MeasureTheory Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The shift `A = [0 1 0; 0 0 1; 0 0 0]` is nilpotent: `Aⁱ = 0` for `i ≥ 3`. -/
private theorem LinearSys.aux_shift3_pow_eq_zero {i : ℕ} (hi : 3 ≤ i) :
    (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) ^ i = 0 :=
  pow_eq_zero_of_le hi (by
    ext j k; fin_cases j <;> fin_cases k <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three])

/-- The shift's flow, coordinatewise: `e^{tA}x = (x₁ + t x₂ + (t²/2) x₃, x₂ + t x₃, x₃)`. -/
private theorem LinearSys.aux_exp_smul_shift3_mulVec (t : ℝ) (x : Vec ℝ 3) : -- --- CONCL ---
    exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) *ᵥ x =
      ![x 0 + t * x 1 + t ^ 2 / 2 * x 2, x 1 + t * x 2, x 2] := by -- --- PROOF ---
  -- the series stops after its quadratic term
  have hexp : exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) =
      1 + t • !![0, 1, 0; 0, 0, 1; 0, 0, 0] +
        (t ^ 2 / 2) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) ^ 2 := by
    rw [exp_eq_tsum ℝ]
    show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) •
      (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) ^ i = _
    rw [tsum_eq_sum (s := Finset.range 3) fun b hb => by
      rw [smul_pow, LinearSys.aux_shift3_pow_eq_zero (by simp at hb; omega), smul_zero,
        smul_zero]]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, smul_pow]
    simp [Nat.factorial, smul_smul, div_eq_inv_mul, add_assoc]
  rw [hexp]
  ext i; fin_cases i <;>
    simp [sq, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The correction matrix (19) of the shift at `Δt = 1/8`, `η ≥ 2`: its center is `-1/1024` at
`(1, 3)` and zero elsewhere, its radius `1/1024` there plus the remainder bound `E` everywhere. -/
private theorem LinearSys.aux_correctionMatrix_shift3 {η : ℕ} (hη : 2 ≤ η)
    (j k : Fin 3) : -- --- CONCL ---
    (MatExp.correctionMatrix (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) η).center j k =
      (!![0, 0, -1 / 1024; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k ∧
    (MatExp.correctionMatrix (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) η).radius j k =
      (!![0, 0, 1 / 1024; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k +
        MatExp.expRemainderBound ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3))
          η := by -- --- PROOF ---
  -- the `i = 2` term is `-(1/8)²/8 A²`, and every later one is zero
  have hterm : ∀ i : ℕ,
      MatExp.corrTerm (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) (i + 2) j k =
        if i = 0 then (!![0, 0, -1 / 512; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k else 0 := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hcrit : MatExp.corrCoeff 2 = -1 / 4 := by
        simp only [MatExp.corrCoeff, MatExp.corrCritical]
        norm_num [Real.rpow_neg_one]
      have hA2 : (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) ^ 2 =
          !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
        ext j k; fin_cases j <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three]
      simp only [MatExp.corrTerm, hcrit, zero_add, hA2, if_true, Nat.factorial_two]
      fin_cases j <;> fin_cases k <;> norm_num
    · rw [if_neg (by omega)]
      simp [MatExp.corrTerm, LinearSys.aux_shift3_pow_eq_zero (i := i + 2) (by omega)]
  -- so each sum over the orders keeps its first term
  have hsum : ∀ g : ℝ → ℝ, g 0 = 0 →
      ∑ i ∈ Finset.range (η - 1),
        g (MatExp.corrTerm (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) (i + 2) j k) =
        g ((!![0, 0, -1 / 512; 0, 0, 0; 0, 0, 0] : Mat ℝ 3 3) j k) := by
    intro g hg
    obtain ⟨m, hm⟩ : ∃ m, η - 1 = m + 1 := ⟨η - 2, by omega⟩
    rw [hm, Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by
      rw [hterm, if_neg (by omega), hg]]
    rw [hterm, if_pos rfl, zero_add]
  simp only [Interval.center, Interval.radius, MatExp.correctionMatrix, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  rw [hsum (fun r => min r 0) (by simp), hsum (fun r => max r 0) (by simp)]
  fin_cases j <;> fin_cases k <;> norm_num <;> ring

/-- The remainder bound of the correction matrix at `Δt = 1/8`, `η ≥ 2`, lies in
`[0, 1/2976]`. -/
private theorem LinearSys.aux_expRemainderBound_shift3 {η : ℕ} (hη : 2 ≤ η) : -- --- CONCL ---
    0 ≤ MatExp.expRemainderBound ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) η ∧
      MatExp.expRemainderBound ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) η ≤
        1 / 2976 := by -- --- PROOF ---
  -- `‖A/8‖∞ ≤ 1/8`, the largest row sum
  have hn : ‖(1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)‖ ≤ 1 / 8 := by
    rw [Matrix.linfty_opNorm_def]
    have : ((Finset.univ : Finset (Fin 3)).sup fun i =>
        ∑ j, ‖((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) i j‖₊) ≤
          (1 / 8 : NNReal) := by
      apply Finset.sup_le; intro i _
      fin_cases i <;> simp [Fin.sum_univ_three]
    exact_mod_cast this
  set x := ‖(1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hη' : (2 : ℝ) ≤ η := by exact_mod_cast hη
  -- the geometric factor is at most `32/31`
  have hq : 31 / 32 ≤ 1 - x / ((η : ℝ) + 2) := by
    rw [le_sub_comm, div_le_iff₀ (by linarith)]
    nlinarith
  have hq0 : 0 < 1 - x / ((η : ℝ) + 2) := by linarith
  have hinv : (1 - x / ((η : ℝ) + 2))⁻¹ ≤ 32 / 31 := by
    rw [inv_le_comm₀ hq0 (by norm_num)]; linarith
  -- `x^{η+1}/(η+1)! ≤ (1/8)³/3! = 1/3072`
  have hpow : x ^ (η + 1) ≤ (1 / 8) ^ 3 :=
    calc x ^ (η + 1) ≤ (1 / 8) ^ (η + 1) := pow_le_pow_left₀ hx0 hn _
      _ ≤ (1 / 8) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hfac : (6 : ℝ) ≤ (Nat.factorial (η + 1) : ℝ) := by
    have := Nat.factorial_le (show 3 ≤ η + 1 by omega)
    exact_mod_cast this
  have hfrac : x ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) ≤ 1 / 3072 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hx0 (η + 1)]
  have hfrac0 : 0 ≤ x ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) :=
    div_nonneg (pow_nonneg hx0 _) (by positivity)
  refine ⟨mul_nonneg hfrac0 (inv_nonneg.mpr hq0.le), ?_⟩
  calc x ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) * (1 - x / ((η : ℝ) + 2))⁻¹
      ≤ 1 / 3072 * (32 / 31) :=
        mul_le_mul hfrac hinv (inv_nonneg.mpr hq0.le) (by norm_num)
    _ = 1 / 2976 := by norm_num

/-- `F box(X_end)` (19) of the shift and the box, `η ≥ 2`, answers a direction `a` with at most
`-a(e₁)/4 + 27/80 |a(e₁)| + 9/100 (|a(e₂)| + |a(e₃)|)`. -/
private theorem LinearSys.aux_supportBound_shift3 {η : ℕ} (hη : 2 ≤ η)
    (a : Vec ℝ 3 →ₗ[ℝ] ℝ) : -- --- CONCL ---
    ((Zonotope.mtimesIntervalMat
      (MatExp.correctionMatrix (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) η)
      (⟨![-1, -1 / 4, 1023 / 4], ![1, 1 / 4, 1025 / 4]⟩ : Interval (Vec ℝ 3)).zonotope).supportBound
        a).val ≤
      -(a (Pi.single 0 1)) / 4 + 27 / 80 * |a (Pi.single 0 1)| +
        9 / 100 * (|a (Pi.single 1 1)| + |a (Pi.single 2 1)|) := by -- --- PROOF ---
  obtain ⟨hE0, hE1⟩ := LinearSys.aux_expRemainderBound_shift3 hη
  have hC := LinearSys.aux_correctionMatrix_shift3 hη
  set C := MatExp.correctionMatrix (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3) (1 / 8) η
  set B := (⟨![-1, -1 / 4, 1023 / 4], ![1, 1 / 4, 1025 / 4]⟩ : Interval (Vec ℝ 3)).zonotope
  set E := MatExp.expRemainderBound ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) η
  -- `a` by its values on the unit vectors
  have ha : ∀ v : Vec ℝ 3, a v = v 0 * a (Pi.single 0 1) + v 1 * a (Pi.single 1 1) +
      v 2 * a (Pi.single 2 1) := by
    intro v
    have hs : ∀ i : Fin 3, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 :=
      fun i => by funext j; simp [Pi.single_apply, eq_comm]
    rw [LinearMap.pi_apply_eq_sum_univ a v, Fin.sum_univ_three]
    simp only [hs, smul_eq_mul]
  -- the center `F_c box_c = (-1/4, 0, 0)` and the center's images of the box's generators
  have hc : C.center *ᵥ B.c = ![-1 / 4, 0, 0] := by
    ext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, (hC _ _).1, B, Interval.zonotope]
    all_goals norm_num
  have hg : ∀ l : Fin 3, C.center *ᵥ B.G l = ![if l = 2 then -1 / 4096 else 0, 0, 0] := by
    intro l; ext i; fin_cases l <;> fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, (hC _ _).1, B, Interval.zonotope]
    all_goals norm_num
  -- the box's absolute bounds `(1, 1/4, 1025/4)`, and the boxing radii
  have hab : ∀ k, B.absBound k = ![1, 1 / 4, 1025 / 4] k := by
    intro k
    show |B.c k| + ∑ l : Fin 3, |B.G l k| = _
    fin_cases k <;> simp [Fin.sum_univ_three, B, Interval.zonotope] <;> norm_num
  have hr : ∀ i, Zonotope.radiusReach C B i =
      (if i = 0 then 1025 / 4096 else 0) + E * (1030 / 4) := by
    intro i
    simp only [Zonotope.radiusReach, Fin.sum_univ_three, hab, (hC _ _).2]
    fin_cases i <;> simp <;> ring
  -- the support value, generator by generator: the boxing generators are `rᵢ eᵢ`
  have hdiag : ∀ i : Fin 3, a ((Matrix.diagonal fun i => Zonotope.radiusReach C B i) i) =
      Zonotope.radiusReach C B i * a (Pi.single i 1) := by
    intro i
    rw [ha, ha (Pi.single i 1)]
    fin_cases i <;> simp
  -- the center's term, then the `3 + 3` generators split at the append
  have hval : ((Zonotope.mtimesIntervalMat C B).supportBound a).val =
      a (C.center *ᵥ B.c) + ∑ l : Fin 3, |a (C.center *ᵥ B.G l)| +
        ∑ i : Fin 3, |a ((Matrix.diagonal fun i => Zonotope.radiusReach C B i) i)| := by
    show a (C.center *ᵥ B.c) + ∑ x : Fin (B.h + 3), |a (Fin.append (fun l => C.center *ᵥ B.G l)
      (Matrix.diagonal fun i => Zonotope.radiusReach C B i) x)| = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, add_assoc]
    rfl
  have hv : ∀ x y z : ℝ, a ![x, y, z] =
      x * a (Pi.single 0 1) + y * a (Pi.single 1 1) + z * a (Pi.single 2 1) := fun x y z => by
    rw [ha]; simp
  -- everything in the three values of `a` and `E`, which `E ≤ 1/2976` bounds
  rw [hval, hc, Fin.sum_univ_three, Fin.sum_univ_three, hg, hg, hg, hdiag, hdiag, hdiag, hr, hr,
    hr, hv, hv, hv, hv]
  generalize a (Pi.single 0 1) = e₀ at *
  generalize a (Pi.single 1 1) = e₁ at *
  generalize a (Pi.single 2 1) = e₂ at *
  have hr0 : (0 : ℝ) ≤ 1025 / 4096 + E * (515 / 2) := by nlinarith
  norm_num [abs_mul, Fin.ext_iff, abs_of_nonneg hE0, abs_of_nonneg hr0]
  have p0 := abs_nonneg e₀
  have p1 := abs_nonneg e₁
  have p2 := abs_nonneg e₂
  nlinarith [mul_le_mul_of_nonneg_right hE1 p0, mul_le_mul_of_nonneg_right hE1 p1,
    mul_le_mul_of_nonneg_right hE1 p2]

/-- `µ` (22), line 3, for the shift and the box at `Δt = 1/8` is at most `1/9`: the images of the
generators have lengths `0`, `1/32` and at most `157/5000`. -/
private theorem LinearSys.aux_maxBackReachMu_shift3 : -- --- CONCL ---
    (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)).maxBackReachMu (1 / 8)
      (⟨![-1, -1 / 4, 1023 / 4], ![1, 1 / 4, 1025 / 4]⟩ : Interval (Vec ℝ 3)).zonotope ≤
        1 / 9 := by -- --- PROOF ---
  set B := (⟨![-1, -1 / 4, 1023 / 4], ![1, 1 / 4, 1025 / 4]⟩ : Interval (Vec ℝ 3)).zonotope
  set M := exp ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) - 1
  -- line 3's spectral norm is the induced norm of the generators' images
  have hmat : M * (Matrix.of fun i j => B.G j i : Matrix (Fin 3) (Fin B.h) ℝ) =
      Matrix.of fun i j => (M *ᵥ B.G j) i := by
    ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  set g := genOpNorm₂ fun j => M *ᵥ B.G j
  have hμ : (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)).maxBackReachMu
      (1 / 8) B = Real.sqrt 3 * g := by
    simp only [LinearSys.maxBackReachMu]
    rw [show toRealMat (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)).A =
      !![0, 1, 0; 0, 0, 1; 0, 0, 0] from rfl]
    rw [hmat]
    rfl
  -- the images `0`, `(1/32, 0, 0)` and `(1/512, 1/32, 0)`, their lengths summed
  have himg : ∀ j : Fin 3, M *ᵥ B.G j =
      (![![0, 0, 0], ![1 / 32, 0, 0], ![1 / 512, 1 / 32, 0]] : Fin 3 → Vec ℝ 3) j := by
    intro j
    rw [show M *ᵥ B.G j = exp ((1 / 8 : ℝ) • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) *ᵥ B.G j
      - B.G j by simp [M, Matrix.sub_mulVec], LinearSys.aux_exp_smul_shift3_mulVec]
    fin_cases j <;> ext i <;> fin_cases i <;> simp [B, Interval.zonotope] <;> norm_num
  have hg : g ≤ 1 / 32 + 157 / 5000 := by
    refine (genOpNorm₂_le_sum_norm₂ _).trans ?_
    show ∑ j : Fin 3, ‖M *ᵥ B.G j‖₂ ≤ _
    rw [Fin.sum_univ_three, himg, himg, himg]
    simp only [norm₂, Fin.sum_univ_three]
    simp
    have e2 : Real.sqrt ((1 / 512) ^ 2 + (1 / 32) ^ 2) ≤ 157 / 5000 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have e1 : Real.sqrt ((1 / 32) ^ 2) = 1 / 32 := Real.sqrt_sq (by norm_num)
    norm_num at e1 e2 ⊢
    linarith
  -- `√3 (1/32 + 157/5000) ≤ 1/9`
  have hg0 : 0 ≤ g := genOpNorm₂_nonneg _
  rw [hμ]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  nlinarith [mul_nonneg hs0 hg0, mul_le_mul_of_nonneg_left hg hs0]

/-- A point lies in `(X ⊖ F box) ⊖ B_µ`, lines 4-5, when every row `a` of `X` leaves room for the
bound `g a` on `F box` and for `µ ≤ 1/9` times `101/100 ≥ ‖a‖₂`. -/
private theorem LinearSys.aux_mem_maxBackReachPoly (X : HPolytope (Vec ℝ 3))
    (FB : Zonotope (Vec ℝ 3)) (g : (Vec ℝ 3 →ₗ[ℝ] ℝ) → ℝ)
    (hFB : ∀ a, (FB.supportBound a).val ≤ g a) {μ : ℝ} (hμ : μ ≤ 1 / 9) (x : Vec ℝ 3)
    (heq : ∀ i, X.Ae i x = X.be i)
    (hnorm : ∀ i, ∑ j, X.A i (Pi.single j 1) ^ 2 ≤ (101 / 100) ^ 2)
    (hrow : ∀ i, X.A i x + g (X.A i) + 101 / 900 ≤ X.b i) : -- --- CONCL ---
    let XF := X.minkDiffOf FB.construct fun i => FB.supportBound (X.A i)
    x ∈ (XF.minkDiffOf (⟨0, 0, μ⟩ : Capsule 3).construct
      fun i => (⟨0, 0, μ⟩ : Capsule 3).supportBound (XF.A i)).construct := by -- --- PROOF ---
  intro XF
  refine ⟨fun i => ?_, heq⟩
  show X.A i x ≤ X.b i - (FB.supportBound (X.A i)).val -
    ((X.A i) 0 + |(X.A i) 0| + μ * Real.sqrt (∑ j, X.A i (Pi.single j 1) ^ 2))
  have hs : Real.sqrt (∑ j, X.A i (Pi.single j 1) ^ 2) ≤ 101 / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, hnorm i⟩
  have hs0 := Real.sqrt_nonneg (∑ j, X.A i (Pi.single j 1) ^ 2)
  have := hFB (X.A i)
  have := hrow i
  rw [map_zero, abs_zero, add_zero, zero_add]
  nlinarith [mul_le_mul hμ hs hs0 (by norm_num : (0 : ℝ) ≤ 1 / 9)]

/-- No run from `(7/4, -16, 256)` with zero input and disturbance meets the box in `[0, 1/8]`: its
first coordinate is `5/4 + 128(t - 1/16)² > 1`. -/
private theorem LinearSys.aux_not_mem_timeIntervalBackReach_shift3 (Xend : HPolytope (Vec ℝ 3))
    (hX : ∀ x ∈ Xend.construct, x 0 ≤ 1) : -- --- CONCL ---
    ![7 / 4, -16, 256] ∉ LinearSys.timeIntervalBackReachSetExistsForallExact (S := 𝒮)
      (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3))
        (Icc 0 (1 / 8)) {0} {0} Xend.construct (Icc 0 (1 / 8)) := by -- --- PROOF ---
  rintro ⟨u, hu, humeas, hall⟩
  obtain ⟨x, traj, hx0, t, ht, hxt⟩ :=
    hall (fun _ => 0) (fun _ _ => rfl) aestronglyMeasurable_const
  -- the run restricted to `[0, t]`
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (1 / 8) := Icc_subset_Icc le_rfl ht.2
  have traj' : LinearSys.IsPerturbedTrajectory (S := 𝒮)
      (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3))
      (Icc 0 t) {0} {0} x u (fun _ => 0) :=
    { input := fun s hs => traj.input s (hsub hs)
      disturbance := fun s hs => traj.disturbance s (hsub hs)
      measInput := traj.measInput.mono_measure (Measure.restrict_mono hsub le_rfl)
      measDisturbance := traj.measDisturbance.mono_measure (Measure.restrict_mono hsub le_rfl)
      cont := traj.cont.mono hsub
      flow := fun s hs => traj.flow s (hsub hs) }
  have hsup := traj'.superposition (S := 𝒮) ht.1 Bornology.isBounded_singleton
    Bornology.isBounded_singleton
  -- the input is zero on `[0, t]`, so both integrals vanish
  have hu0 : (∫ s in (0 : ℝ)..t, exp ((t - s) • toRealMat
      (LinearSys.canonical (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)).A) *ᵥ u s) = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : Vec ℝ 3)) fun s hs => ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le ht.1] at hs
    show _ *ᵥ u s = 0
    rw [show u s = 0 from hu s (hsub hs), Matrix.mulVec_zero]
  rw [hu0, hx0] at hsup
  simp only [Matrix.mulVec_zero, intervalIntegral.integral_zero, add_zero] at hsup
  have h0 := hX _ hxt
  rw [hsup] at h0
  change (exp (t • (!![0, 1, 0; 0, 0, 1; 0, 0, 0] : Mat ℝ 3 3)) *ᵥ ![7 / 4, -16, 256]) 0 ≤ 1 at h0
  rw [LinearSys.aux_exp_smul_shift3_mulVec] at h0
  simp at h0
  nlinarith [sq_nonneg (t - 1 / 16)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachTimeInterval_inner_counterexample (η : ℕ)
    (hη : 2 ≤ η) : -- --- CONCL ---
    let A : Mat ℝ 3 3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    let sys : LinearSys ℝ 3 := LinearSys.canonical A
    let Δt : ℝ := 1 / 8                                     -- τ = [t₀, t_end] = [0, 1/8], σ = 1
    let Xend : HPolytope (Vec ℝ 3) :=                       -- the box ⟨H, d⟩_H
      ⟨6, ![LinearMap.proj 0, LinearMap.proj 1, LinearMap.proj 2,
          -LinearMap.proj 0, -LinearMap.proj 1, -LinearMap.proj 2],
        ![1, 1 / 4, 1025 / 4, 1, 1 / 4, -1023 / 4], 0, ![], ![]⟩
    let B := (⟨![-1, -1 / 4, 1023 / 4], ![1, 1 / 4, 1025 / 4]⟩ :
      Interval (Vec ℝ 3)).zonotope                          -- box(X_end)
    let FB := Zonotope.mtimesIntervalMat
      (MatExp.correctionMatrix A Δt η) B                    -- F box(X_end), (19)
    let μ := sys.maxBackReachMu Δt B                        -- 3. µ, (22)
    let Bμ : Capsule 3 := ⟨0, 0, μ⟩
    let XF₁ := Xend.minkDiffOf FB.construct fun i => FB.supportBound (Xend.A i)
    let P₁ := XF₁.minkDiffOf Bμ.construct
      fun i => Bμ.supportBound (XF₁.A i)                    -- 4. P₁ = (X_end ⊖ F box) ⊖ B_µ
    let X₂ := Xend.comap (exp (-(Δt • A))).mulVecLin        -- e^{AΔt}X_end
    let XF₂ := X₂.minkDiffOf FB.construct fun i => FB.supportBound (X₂.A i)
    let P₂ := XF₂.minkDiffOf Bμ.construct
      fun i => Bμ.supportBound (XF₂.A i)                    -- 5. P₂ = (e^{AΔt}X_end ⊖ F box) ⊖ B_µ
    let R := (exp ((-Δt) • A) *ᵥ ·) ''
      convexHull ℝ (P₁.construct ∪ P₂.construct)            -- 11.-12., (54) at k = 0, U = W = {0}
    ![7 / 4, -16, 256] ∈ R ∧
      ![7 / 4, -16, 256] ∉ sys.timeIntervalBackReachSetExistsForallExact (S := 𝒮)
        (Icc 0 Δt) {0} {0} Xend.construct (Icc 0 Δt) := by -- --- PROOF ---
  intro A sys Δt Xend B FB μ Bμ XF₁ P₁ X₂ XF₂ P₂ R
  have hμ := LinearSys.aux_maxBackReachMu_shift3
  have hFB := LinearSys.aux_supportBound_shift3 hη
  -- `e^{-AΔt}x = (x₁ - x₂/8 + x₃/128, x₂ - x₃/8, x₃)`
  have hM : ∀ x : Vec ℝ 3,
      exp (-(Δt • A)) *ᵥ x = ![x 0 - x 1 / 8 + x 2 / 128, x 1 - x 2 / 8, x 2] := fun x => by
    rw [← neg_smul, LinearSys.aux_exp_smul_shift3_mulVec]
    ext i; fin_cases i <;> norm_num [Δt] <;> ring
  refine ⟨?_, LinearSys.aux_not_mem_timeIntervalBackReach_shift3 Xend fun x hx => by
    simpa [Xend] using hx.1 0⟩
  -- `x₀ = (3/4, 0, 256)` is in `P₁`
  have h₁ : (![3 / 4, 0, 256] : Vec ℝ 3) ∈ P₁.construct :=
    LinearSys.aux_mem_maxBackReachPoly Xend FB _ hFB hμ _ (fun i => i.elim0)
      (fun i => by fin_cases i <;> simp [Xend, Fin.sum_univ_three] <;> norm_num)
      (fun i => by
        fin_cases i <;> simp [Xend] <;> norm_num)
  -- `e^{AΔt}x₀ = (11/4, 32, 256)` is in `P₂`
  have hX₂ : ∀ i v, X₂.A i v = Xend.A i ![v 0 - v 1 / 8 + v 2 / 128, v 1 - v 2 / 8, v 2] :=
    fun i v => by
      show Xend.A i (exp (-(Δt • A)) *ᵥ v) = _
      rw [hM]
  have h₂ : (![11 / 4, 32, 256] : Vec ℝ 3) ∈ P₂.construct :=
    LinearSys.aux_mem_maxBackReachPoly X₂ FB _ hFB hμ _ (fun i => i.elim0)
      (by
        simp only [hX₂, Fin.sum_univ_three]
        show ∀ i : Fin 6, _
        simp [Fin.forall_fin_succ, Xend]
        norm_num)
      (by
        simp only [hX₂]
        show ∀ i : Fin 6, _ ≤ Xend.b i
        simp [Fin.forall_fin_succ, Xend]
        norm_num)
  -- their midpoint `(7/4, 16, 256)`, mapped by `e^{-AΔt}`
  refine ⟨![7 / 4, 16, 256], segment_subset_convexHull (mem_union_left _ h₁)
    (mem_union_right _ h₂) ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩, ?_⟩
  · ext i; fin_cases i <;> simp <;> norm_num
  · show exp ((-Δt) • A) *ᵥ ![7 / 4, 16, 256] = ![7 / 4, -16, 256]
    rw [neg_smul, hM]
    ext i; fin_cases i <;> simp <;> norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
