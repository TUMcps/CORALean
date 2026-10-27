module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerCurvatureError
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerLagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffStep
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpRemainderMatShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpSmulShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerAbstrErrShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The inner algorithm's line 15 shifts the time-point set out of the reachable set

[1, Alg. 1] computes `R̂(t_{k+1})` in line 15 as `R_aff ⊖ R̂_err` shifted by `2c`, `c = cen(C) +
cen(R̂_err)`, where `Prop. 1` shifts by `2 cen(R̂_err)` alone. For a linear field, where
`R̂_err = {0}`, line 15 gives `R(t_{k+1}) + 2 cen(C)`. One step, `Δt = 1`, of `ẋ = (x₂, 1)` from
`X₀ = [-1/10, 1/10]²`, Taylor order `η ≥ 1`: `x* = (0, 1/2)`, `w = (1/2, 1)`, `A = [0 1; 0 0]`,
`F = {0}`, `G` has `[-1/8, 0]` at `(1, 2)`, so `C = [-1/8, 0] × {0}` (17), centered at
`(-1/16, 0)`. `D²f ≡ 0` gives `L̂ = 0` (9), `R̂_err = {0}` (13), `R_con = (1, 1)`, so `R_aff` is
the exact `R(1)`. Line 15 holds `(3/8, 1)`, whose preimage under the flow is `(-1/8, 0) ∉ X₀`.
(17) comes from `innerCurvatureError`; `shearDriftOps` meets the theorem's hypotheses (`_instance`).

## Inputs
* `ops` – subroutine operations
* `η` – Taylor order
* `fuel` – iteration bound of the remainder loop
* `U` – input set

## Hypotheses
* `hη` – Taylor order positive
* `hfuel` – iteration bound positive
* `hcen` – the box's center, a Chebyshev center of it, is `cen(X₀)`
* `hcen0` – a point is its own center
* `hcenC` – the center of the segment `[-1/8, 0] × {0}`
* `hjac` – (6): the field's Jacobian `A` everywhere
* `hbox` – the box of the start set is nonempty
* `hcurv` – `curv` is the curvature error (17)
* `herr` – `err` is the abstraction error (13)
* `hlagr` – `lagr` is the Lagrange remainder (9) of the field
* `hzero` – line 9's interval `[0, 0]` is the set `{0}`
* `hsmul` – line 11's `μL` scales the set
* `hsub` – line 13's test is the inclusion `L ⊆ L̂`

## Conclusion
* line 15's `R̂(t_{k+1})` holds a state no run reaches at `t_k + Δt`

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Pointwise Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


/-- The least `i`-th coordinate of a set, the lower end of its interval hull. -/
noncomputable def NonlinearSys.hullLo (S : Set (Vec ℝ 2)) (i : Fin 2) : ℝ :=
  sInf ((fun x : Vec ℝ 2 => x i) '' S)

/-- The greatest `i`-th coordinate of a set, the upper end of its interval hull. -/
noncomputable def NonlinearSys.hullHi (S : Set (Vec ℝ 2)) (i : Fin 2) : ℝ :=
  sSup ((fun x : Vec ℝ 2 => x i) '' S)

open Classical in
/-- The subroutines of the inner algorithm for `ẋ = (x₂, 1)`: `box` the interval hull, `cen` its
midpoint (the Chebyshev center of a box), `jac` the field's Jacobian, `curv`, `err`, `lagr` as
(17), (13) and (9), `L` a set with `μL` its scaling and the inclusion as line 13's test. -/
noncomputable def NonlinearSys.shearDriftOps (η : ℕ) :
    NonlinearSys.InnerMinkDiffOps 2 (Set (Vec ℝ 2)) where
  cen S := fun i => (NonlinearSys.hullLo S i + NonlinearSys.hullHi S i) / 2
  box S := Icc (NonlinearSys.hullLo S) (NonlinearSys.hullHi S)
  jac _ := !![0, 1; 0, 0]
  curv := NonlinearSys.innerCurvatureError η
  err := NonlinearSys.innerAbstrErr η
  lagr := NonlinearSys.innerLagrangeRemainder fun x => ![x 1, 1]
  zero := {0}
  smul μ L := μ • L
  sub L L' := decide (L ⊆ L')


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- (9): `L = [0, 0]` for the affine `f(x) = (x₂, 1)`, as `D²f ≡ 0`. -/
private theorem NonlinearSys.aux_lagrange_shearDrift (xstar : Vec ℝ 2)
    (X : Set (Vec ℝ 2)) : -- --- CONCL ---
    NonlinearSys.innerLagrangeRemainder (fun x : Vec ℝ 2 => (![x 1, 1] : Vec ℝ 2)) xstar X =
      {0} := by -- --- PROOF ---
  let L : Vec ℝ 2 →L[ℝ] Vec ℝ 2 := LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 1; 0, 0])
  have hf : (fun x : Vec ℝ 2 => (![x 1, 1] : Vec ℝ 2)) = fun x => L x + ![0, 1] := by
    funext y; ext i; fin_cases i <;> simp [L, dotProduct, Fin.sum_univ_two]
  have hD : fderiv ℝ (fderiv ℝ fun x : Vec ℝ 2 => L x + ![0, 1]) = 0 := by
    rw [show fderiv ℝ (fun x : Vec ℝ 2 => L x + ![0, 1]) = fun _ => L from
      funext fun x => by rw [fderiv_add_const]; exact L.fderiv]
    funext y; exact fderiv_const_apply L
  simp only [NonlinearSys.innerLagrangeRemainder, hf, hD, Pi.zero_apply, _root_.zero_apply,
    abs_zero, Real.iSup_const_zero]
  have hl : (fun i : Fin 2 => (fun j => ⨆ y ∈ X, |y j - xstar j|) ⬝ᵥ
      ((fun _ _ => (0 : ℝ)) *ᵥ fun j => ⨆ y ∈ X, |y j - xstar j|) / 2) = 0 := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hl, neg_zero, Set.Icc_self]


/-- `R_con = ∫₀¹ e^{(1-θ)A} (1/2, 1) dθ = (1, 1)` for the shear `A`. -/
private theorem NonlinearSys.aux_rcon_shearDrift : -- --- CONCL ---
    ∫ θ in (0 : ℝ)..1, exp ((1 - θ) • (!![0, 1; 0, 0] : Mat ℝ 2 2)) *ᵥ (![1 / 2, 1] : Vec ℝ 2) =
      ![1, 1] := by -- --- PROOF ---
  have hint : ∀ θ : ℝ, exp ((1 - θ) • (!![0, 1; 0, 0] : Mat ℝ 2 2)) *ᵥ (![1 / 2, 1] : Vec ℝ 2) =
      (![1 / 2, 1] : Vec ℝ 2) + (1 - θ) • (![1, 0] : Vec ℝ 2) := fun θ => by
    rw [NonlinearSys.exp_smul_shear]
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  simp only [hint]
  rw [intervalIntegral.integral_add (by simp) (by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)),
    intervalIntegral.integral_smul_const]
  have h1 : ∫ θ in (0 : ℝ)..1, (1 - θ) = 1 / 2 := by
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp [integral_id]
    norm_num
  rw [h1]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  ext i; fin_cases i <;> norm_num


/-- A run of `ẋ = (x₂, 1)` on `[0, t]` is `x s = (x₀₁ + s x₀₂ + s²/2, x₀₂ + s)`. -/
private theorem NonlinearSys.aux_eq_of_hasDerivWithinAt_shearDrift2 {x : ℝ → Vec ℝ 2} {t : ℝ}
    (hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt x ![x s 1, 1] (Icc 0 t) s) : -- --- CONCL ---
    ∀ s ∈ Icc 0 t, x s 1 = x 0 1 + s ∧ x s 0 = x 0 0 + s * x 0 1 + s ^ 2 / 2 := by -- --- PROOF ---
  -- a function with zero derivative on `[0, t]` is constant there
  have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc 0 t, HasDerivWithinAt g 0 (Icc 0 t) s) →
      ∀ s ∈ Icc 0 t, g s = g 0 := fun g hg =>
    constant_of_has_deriv_right_zero (fun s hs => (hg s hs).continuousWithinAt)
      (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  have hc : ∀ i, ∀ s ∈ Icc 0 t,
      HasDerivWithinAt (fun s => x s i) ((![x s 1, 1] : Vec ℝ 2) i) (Icc 0 t) s :=
    fun i s hs => hasDerivWithinAt_pi.mp (hd s hs) i
  -- `x₂ - s` is constant, and `x₁ - s x₀₂ - s²/2` then as well
  have h1 : ∀ s ∈ Icc 0 t, x s 1 - s = x 0 1 - 0 :=
    hconst (fun s => x s 1 - s) fun s hs =>
      ((hc 1 s hs).sub (hasDerivWithinAt_id s (Icc 0 t))).congr_deriv (by simp)
  have h0 : ∀ s ∈ Icc 0 t, x s 0 - s * x 0 1 - s ^ 2 / 2 =
      x 0 0 - 0 * x 0 1 - 0 ^ 2 / 2 := by
    refine hconst (fun s => x s 0 - s * x 0 1 - s ^ 2 / 2) fun s hs => ?_
    have hx : HasDerivWithinAt (fun s => x s 0) (x s 1) (Icc 0 t) s := by
      simpa using hc 0 s hs
    have h2 := (hx.sub ((hasDerivWithinAt_id s (Icc 0 t)).mul_const (x 0 1))).sub
      (((hasDerivWithinAt_id s (Icc 0 t)).pow 2).div_const 2)
    refine h2.congr_deriv ?_
    have := h1 s hs
    simp only [id]
    linarith
  intro s hs
  refine ⟨by linarith [h1 s hs], by linarith [h0 s hs]⟩


/-- `X₀ = [-1/10, 1/10]²`, coordinatewise. -/
private theorem NonlinearSys.aux_mem_box_shearDrift2 (y : Vec ℝ 2) :
    y ∈ Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10] ↔
      (-1 / 10 ≤ y 0 ∧ y 0 ≤ 1 / 10) ∧ (-1 / 10 ≤ y 1 ∧ y 1 ≤ 1 / 10) := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto


/-- The `i`-th coordinate of a box `[a, b]` ranges over `[a i, b i]`. -/
private theorem NonlinearSys.aux_coord_Icc {a b : Vec ℝ 2} (hab : a ≤ b)
    (i : Fin 2) : -- --- CONCL ---
    (fun x : Vec ℝ 2 => x i) '' Icc a b = Icc (a i) (b i) := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1 i, hx.2 i⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Function.update a i y, ⟨?_, ?_⟩, by simp⟩
    · intro j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · simp [hj]
    · intro j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simp [hj, hab j]

/-- The interval hull of a box is the box. -/
private theorem NonlinearSys.aux_hull_Icc {a b : Vec ℝ 2} (hab : a ≤ b) (i : Fin 2) :
    NonlinearSys.hullLo (Icc a b) i = a i ∧ NonlinearSys.hullHi (Icc a b) i = b i := by
  unfold NonlinearSys.hullLo NonlinearSys.hullHi
  rw [NonlinearSys.aux_coord_Icc hab i]
  exact ⟨csInf_Icc (hab i), csSup_Icc (hab i)⟩


/-- (17): `C = F box(X₀) ⊕ G w = [-1/8, 0] × {0}` for the shear `A`, `Δt = 1`, `w = (1/2, 1)`, a
Taylor order `η ≥ 1` and a nonempty box: `F = {0}`, and `G` is `0` but for the `(1, 2)` entry
`[-1/8, 0]`, the `i = 0` term `corrCoeff 2 / 2! · A`. -/
private theorem NonlinearSys.aux_curvature_shearDrift {η : ℕ} (hη : 1 ≤ η)
    {B : Set (Vec ℝ 2)} (hB : B.Nonempty) : -- --- CONCL ---
    NonlinearSys.innerCurvatureError η 1 !![0, 1; 0, 0] B ![1 / 2, 1] =
      Icc ![-1 / 8, 0] ![0, 0] := by -- --- PROOF ---
  -- `F = {0}`
  have hT : ∀ i j k, Real.MatExp.corrTerm !![0, 1; 0, 0] 1 (i + 2) j k = 0 := fun i j k => by
    simp [Real.MatExp.corrTerm, NonlinearSys.shear_pow_eq_zero (i := i + 2) (by omega)]
  have hF : (STL.depCurvatureF !![0, 1; 0, 0] 1 η).construct = {0} := by
    ext M
    simp only [Real.Interval.construct, STL.depCurvatureF, hT,
      NonlinearSys.expRemainderMat_shear 1 hη, min_self, max_self, Finset.sum_const_zero,
      Matrix.zero_apply, sub_zero, add_zero, mem_setOf_eq, mem_singleton_iff, Entrywise.entry_mat]
    constructor
    · intro h; ext j k; exact le_antisymm (h (j, k)).2 (h (j, k)).1
    · rintro rfl p; simp
  -- the terms of `G`: only `i = 0` is not zero, `-A/8`, as `corrCoeff 2 = -1/4`
  have hcrit : Real.MatExp.corrCoeff 2 = -1 / 4 := by
    simp only [Real.MatExp.corrCoeff, Real.MatExp.corrCritical]
    norm_num [Real.rpow_neg_one]
  have hterm : ∀ i j k, Real.MatExp.constCorrTerm !![0, 1; 0, 0] 1 i j k =
      if i = 0 then -(!![0, 1; 0, 0] : Mat ℝ 2 2) j k / 8 else 0 := fun i j k => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [Real.MatExp.constCorrTerm, hcrit, zero_add, pow_one, if_true, Nat.factorial_two]
      push_cast; ring
    · rw [if_neg (by omega)]
      simp [Real.MatExp.constCorrTerm,
        NonlinearSys.shear_pow_eq_zero (i := i + 1) (by omega)]
  have hsum : ∀ g : ℝ → ℝ, g 0 = 0 → ∀ j k, ∑ i ∈ Finset.range η,
      g (Real.MatExp.constCorrTerm !![0, 1; 0, 0] 1 i j k) =
        g (-(!![0, 1; 0, 0] : Mat ℝ 2 2) j k / 8) := fun g hg j k => by
    rw [Finset.sum_eq_single 0]
    · rw [hterm, if_pos rfl]
    · intro i _ hi; rw [hterm, if_neg hi, hg]
    · intro h; exact absurd (Finset.mem_range.mpr hη) h
  -- `G w`: `G` is zero but for the `(1, 2)` entry `[-1/8, 0]`, so `N w = (N₁₂, 0)`
  have hG : ⋃ N ∈ (STL.depCurvatureG !![0, 1; 0, 0] 1 η).construct,
      ({N *ᵥ (![1 / 2, 1] : Vec ℝ 2)} : Set (Vec ℝ 2)) = Icc ![-1 / 8, 0] ![0, 0] := by
    -- the matrices of `G`, entrywise
    have hmem : ∀ N : Mat ℝ 2 2, N ∈ (STL.depCurvatureG !![0, 1; 0, 0] 1 η).construct ↔
        (-1 / 8 ≤ N 0 1 ∧ N 0 1 ≤ 0) ∧ N 0 0 = 0 ∧ N 1 0 = 0 ∧ N 1 1 = 0 := fun N => by
      simp only [Real.Interval.construct, STL.depCurvatureG, hsum (fun x => min x 0) (min_self 0),
        hsum (fun x => max x 0) (max_self 0), NonlinearSys.expRemainderMat_shear 1 hη,
        mem_setOf_eq, Entrywise.entry_mat, Matrix.zero_apply, mul_zero, sub_zero, add_zero]
      constructor
      · intro h
        have h00 := h (0, 0)
        have h01 : min (-1 / 8 : ℝ) 0 ≤ N 0 1 ∧ N 0 1 ≤ max (-1 / 8 : ℝ) 0 := by
          simpa using h (0, 1)
        rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at h01
        have h10 := h (1, 0)
        have h11 := h (1, 1)
        simp at h00 h10 h11
        refine ⟨⟨by linarith [h01.1], by linarith [h01.2]⟩, ?_, ?_, ?_⟩ <;> linarith
      · rintro ⟨h01, h00, h10, h11⟩ ⟨j, k⟩
        fin_cases j <;> fin_cases k <;> simp [h00, h10, h11, h01.1, h01.2]
    -- both inclusions
    ext z
    simp only [mem_iUnion, mem_singleton_iff, exists_prop, mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨N, hN, rfl⟩
      obtain ⟨h01, h00, h10, h11⟩ := (hmem N).mp hN
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h10, h11, h01.1, h01.2]
    · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
      refine ⟨!![0, z 0; 0, 0],
        (hmem _).mpr ⟨⟨by simpa using h0, by simpa using h2⟩, rfl, rfl, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
  unfold NonlinearSys.innerCurvatureError
  simp only
  rw [hF, hG]
  simp [hB.image_const]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s line 15, `R̂(t_{k+1})`, for `ẋ = (x₂, 1)` from `[-1/10, 1/10]²` over one step
`Δt = 1`, at any Taylor order `η ≥ 1`, holds `(3/8, 1)`, which no run reaches at `t = 1`; `err` and
`lagr` are (13) and (9), the value of (17) is `[-1/8, 0] × {0}`. -/
theorem NonlinearSys.innerMinkDiffStep_center_counterexample
    (ops : NonlinearSys.InnerMinkDiffOps 2 (Set (Vec ℝ 2))) (η : ℕ) (hη : 1 ≤ η) (fuel : ℕ)
    (hfuel : 0 < fuel) (U : Set (Vec ℝ 1))
    (hcen : ops.cen (Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10]) = 0) (hcen0 : ops.cen {0} = 0)
    (hcenC : ops.cen (Icc ![-1 / 8, 0] ![0, 0]) = ![-1 / 16, 0])
    (hjac : ∀ x, ops.jac x = !![0, 1; 0, 0])
    (hbox : (ops.box (Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10])).Nonempty)
    (hcurv : ops.curv = NonlinearSys.innerCurvatureError η)
    (herr : ops.err = NonlinearSys.innerAbstrErr η)
    (hlagr : ops.lagr = NonlinearSys.innerLagrangeRemainder fun x => ![x 1, 1])
    (hzero : ops.zero = {0}) (hsmul : ∀ μ L, ops.smul μ L = μ • L)
    (hsub : ∀ L L', ops.sub L L' = true ↔ L ⊆ L') : -- --- CONCL ---
    let sys : NonlinearSys 2 1 := ⟨fun x _ => ![x 1, 1], 2, fun x _ => x⟩
    let X₀ : Set (Vec ℝ 2) := Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10]
    ∃ st, NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x 0) 1 (11 / 10) fuel X₀ = some st ∧
      ![3 / 8, 1] ∈ st.Rtk1 ∧ ![3 / 8, 1] ∉ sys.reachSetExact (S := 𝒮) (Icc 0 1) X₀ U
        1 := by -- --- PROOF ---
  intro sys X₀
  set A : Mat ℝ 2 2 := !![0, 1; 0, 0] with hA
  replace hcen : ops.cen X₀ = 0 := hcen
  replace hbox : (ops.box X₀).Nonempty := hbox
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hf0 : sys.f 0 0 = ![0, 1] := by
    ext i; fin_cases i <;> rfl
  have hxstar : ops.cen X₀ + ((1 : ℝ) / 2) • sys.f (ops.cen X₀) 0 = ![0, 1 / 2] := by
    rw [hcen]; show (0 : Vec ℝ 2) + ((1 : ℝ) / 2) • sys.f 0 0 = _
    rw [hf0]; ext i; fin_cases i <;> simp
  have hw : sys.f (![0, 1 / 2] : Vec ℝ 2) 0 = ![1 / 2, 1] := rfl
  -- (17): `C = [-1/8, 0] × {0}`, from the curvature error itself
  have hC : ∀ Y : Set (Vec ℝ 2), Y.Nonempty →
      ops.curv 1 A Y ![1 / 2, 1] = Icc ![-1 / 8, 0] ![0, 0] := fun Y hY => by
    rw [hcurv, hA]; exact NonlinearSys.aux_curvature_shearDrift hη hY
  have hmd : ∀ T : Set (Vec ℝ 2), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  -- the subroutines' values: `R̂_err = {0}` (13), `L = 0` (9)
  have hL : ∀ x D, ops.lagr x D = {0} := fun x D => by
    rw [hlagr]; exact NonlinearSys.aux_lagrange_shearDrift x D
  have hE : ops.err 1 A {0} = {0} := by
    rw [herr, hA]; exact NonlinearSys.innerAbstrErr_shear 1 hη
  have hs : ops.smul (11 / 10) {0} = {0} := by rw [hsmul, Set.smul_set_singleton, smul_zero]
  have hss : ops.sub {0} {0} = true := (hsub _ _).mpr subset_rfl
  have hrem : ∀ Raffτ, NonlinearSys.innerMinkDiffRemainder ops 1 (11 / 10) A ![0, 1 / 2]
      Raffτ {0} (k + 1) = some {0} := fun Raffτ => by
    simp [NonlinearSys.innerMinkDiffRemainder, hs, hE, hL, hss]
  -- `e^{A} = I + A`, as `A² = 0`
  have hexp : exp ((1 : ℝ) • A) = 1 + A := by
    rw [hA, NonlinearSys.exp_smul_shear, one_smul]
  have hRcon : ∫ θ in (0 : ℝ)..1, exp ((1 - θ) • A) *ᵥ (![1 / 2, 1] : Vec ℝ 2) = ![1, 1] := by
    rw [hA]; exact NonlinearSys.aux_rcon_shearDrift
  -- membership in the box, coordinatewise
  have hmem : ∀ y : Vec ℝ 2, y ∈ X₀ ↔
      (-1 / 10 ≤ y 0 ∧ y 0 ≤ 1 / 10) ∧ (-1 / 10 ≤ y 1 ∧ y 1 ≤ 1 / 10) :=
    NonlinearSys.aux_mem_box_shearDrift2
  -- what one step computes: line 15 shifts `R_aff ⊖ {0}` by `2c`, `c = cen(C) + cen({0})`
  have key : ∃ st, NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x 0) 1 (11 / 10) (k + 1) X₀ =
      some st ∧ st.Rtk1 = (fun x => x + (2 : ℝ) • (![-1 / 16, 0] : Vec ℝ 2)) ''
        ((fun x => x + (![1, 1] : Vec ℝ 2)) ''
          ((fun x => (![0, 1 / 2] : Vec ℝ 2) + exp ((1 : ℝ) • A) *ᵥ (x - ![0, 1 / 2])) ''
            X₀)) := by
    unfold NonlinearSys.innerMinkDiffStep
    simp only [hxstar, hw, hjac, hC, Set.image_nonempty, hbox, hzero, hrem, Option.map_some,
      hcenC, hcen0, hE, hmd, hRcon]
    exact ⟨_, rfl, by simp⟩
  obtain ⟨st, hst, hRtk1⟩ := key
  refine ⟨st, hst, ?_, ?_⟩
  · -- the image of `(0, 0) ∈ X₀`: `(-1/2, 0)`, `(1/2, 1)` and the shift `(-1/8, 0)`
    rw [hRtk1]
    have h0 : (![0, 0] : Vec ℝ 2) ∈ X₀ := (hmem _).mpr ⟨by simp; norm_num, by simp; norm_num⟩
    refine ⟨![1 / 2, 1], ⟨![-1 / 2, 0], ⟨![0, 0], h0, ?_⟩, ?_⟩, ?_⟩
    · simp only [hexp]
      simp only [hA]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
      norm_num
    · ext i; fin_cases i <;> simp
      norm_num
    · ext i; fin_cases i <;> simp
      norm_num
  · -- a run ends at `x₂ + 1 = 1`, so starts on `x₂ = 0`, and `x₁ + 1/2 = 3/8` leaves the box
    rintro ⟨x, u, traj, hxt⟩
    have hcont : ContinuousOn (fun s => sys.f (x s) (u s)) (Icc 0 1) := by
      refine continuousOn_pi.mpr fun i => ?_
      fin_cases i
      · exact (continuous_apply 1).comp_continuousOn traj.cont
      · exact continuousOn_const
    have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x s 1, 1] (Icc 0 1) s :=
      fun s hs => traj.hasDerivWithinAt ⟨le_rfl, zero_le_one⟩ hcont hs
    have hx := NonlinearSys.aux_eq_of_hasDerivWithinAt_shearDrift2 hder 1 ⟨zero_le_one, le_rfl⟩
    have e0 := congrFun hxt 0
    have e1 := congrFun hxt 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have hb := ((hmem (x 0)).mp traj.init).1
    rw [hx.1] at e1
    rw [hx.2] at e0
    have h1 : x 0 1 = 0 := by linarith
    rw [h1] at e0
    linarith [hb.1]


/-- [1, Alg. 1]'s line 15 at `shearDriftOps 1` and one pass of the remainder loop: the statement
of `innerMinkDiffStep_center_counterexample` with no hypothesis. -/
theorem NonlinearSys.innerMinkDiffStep_center_counterexample_instance
    (U : Set (Vec ℝ 1)) : -- --- CONCL ---
    let sys : NonlinearSys 2 1 := ⟨fun x _ => ![x 1, 1], 2, fun x _ => x⟩
    let X₀ : Set (Vec ℝ 2) := Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10]
    ∃ st, NonlinearSys.innerMinkDiffStep (NonlinearSys.shearDriftOps 1) (fun x => sys.f x 0) 1
        (11 / 10) 1 X₀ = some st ∧
      ![3 / 8, 1] ∈ st.Rtk1 ∧ ![3 / 8, 1] ∉ sys.reachSetExact (S := 𝒮) (Icc 0 1) X₀ U
        1 := by -- --- PROOF ---
  have hle : (![-1 / 10, -1 / 10] : Vec ℝ 2) ≤ ![1 / 10, 1 / 10] := fun i => by
    fin_cases i <;> norm_num
  have hle2 : (![-1 / 8, 0] : Vec ℝ 2) ≤ ![0, 0] := fun i => by fin_cases i <;> norm_num
  refine NonlinearSys.innerMinkDiffStep_center_counterexample (NonlinearSys.shearDriftOps 1) 1
    le_rfl 1 one_pos U ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl (fun _ _ => rfl) ?_
  · -- the center of the start box is its midpoint `0`
    ext i
    obtain ⟨h1, h2⟩ := NonlinearSys.aux_hull_Icc hle i
    show (NonlinearSys.hullLo _ i + NonlinearSys.hullHi _ i) / 2 = 0
    rw [h1, h2]
    fin_cases i <;> norm_num
  · -- a point is its own center
    ext i
    show (NonlinearSys.hullLo {0} i + NonlinearSys.hullHi {0} i) / 2 = 0
    simp [NonlinearSys.hullLo, NonlinearSys.hullHi]
  · -- the center of the segment `[-1/8, 0] × {0}`
    ext i
    obtain ⟨h1, h2⟩ := NonlinearSys.aux_hull_Icc hle2 i
    show (NonlinearSys.hullLo _ i + NonlinearSys.hullHi _ i) / 2 = _
    rw [h1, h2]
    fin_cases i <;> norm_num
  · -- the Jacobian of the field is `[0 1; 0 0]` everywhere
    intro x; rfl
  · -- the hull of the start box is that box, which is nonempty
    have h : NonlinearSys.hullLo (Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10]) =
        ![-1 / 10, -1 / 10] := funext fun i => (NonlinearSys.aux_hull_Icc hle i).1
    have h' : NonlinearSys.hullHi (Icc ![-1 / 10, -1 / 10] ![1 / 10, 1 / 10]) =
        ![1 / 10, 1 / 10] := funext fun i => (NonlinearSys.aux_hull_Icc hle i).2
    show (Icc (NonlinearSys.hullLo _) (NonlinearSys.hullHi _)).Nonempty
    rw [h, h']
    exact Set.nonempty_Icc.mpr hle
  · -- line 13's test is the inclusion
    intro L L'
    exact @decide_eq_true_iff _ (Classical.propDecidable _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
