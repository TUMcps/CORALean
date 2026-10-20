module

public import CORALean.HybridDynamics.Operations.AbstractionErrorFloat
public import CORALean.HybridDynamics.Theorems.AbstractionErrorDecomp
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.Convex
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.SumTermsMem
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# The float abstraction error encloses the difference of a run and the constant flow

`GuardMap.abstractionError_outer` at floats: for `t ∈ [0, tmax]`, `η ≥ 1`, `th ≥ 0`, `x₀ ∈ R₀` and
a measurable input in `U`, the run of `ẋ = Ax + u` minus the constant flow `x₀ + (Ax₀ + b)t`, `b`
the exact `GuardMap.sdcInput` at the stored centers, is a point of
`GuardMap.abstractionErrorFloat`, provided the float bound `nrm` of `‖tmax A‖` passes `nrm ≤ (η +
2)/2`. `abstractionError_decomp` gives the point as `t(v₁ + v₂ + v₃) + R x₀ + ρ`; each part is a
point of its float set, by the directed powers, `norm_exp_sub_expTaylor_le` and the float
`mtimesIntervalMat`.

## Inputs
* `A` – flow matrix
* `U` – input zonotope
* `R₀` – initial set
* `th` – expansion time
* `tmax` – final time
* `t` – time
* `η` – Taylor order
* `x₀` – initial state
* `u` – input trajectory

## Hypotheses
* `hη` – at least one Taylor term
* `ht` – time within the horizon
* `hth` – expansion time nonnegative
* `hnrm` – float norm bound passes the Taylor test
* `hx₀` – initial state lies in the initial zonotope
* `hU` – input zonotope nonempty
* `hu` – input stays in its set
* `hmeas` – input measurable

## Conclusion
* run minus constant flow lies in the float abstraction error

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix
open NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `s v ∈ [a, b] Z` for `s ∈ [a, b]` and `v ∈ Z`, `[a, b]` the interval matrix `[a, b] I`. -/
theorem aux_absErrFloat_smul_mem {a b : 𝕋} {s : ℝ} (h₁ : toReal a ≤ s) (h₂ : s ≤ toReal b)
    {Z : Zonotope (Vec 𝕋 n)} {v : Vec ℝ n} (hv : v ∈ Z.construct) : -- --- CONCL ---
    s • v ∈ (Zonotope.mtimesIntervalMat (Interval.smul a b
      (Interval.point (diagonalBlock fun _ => (one : 𝕋)))) Z).construct := by -- --- PROOF ---
  have hone : (1 : Mat ℝ n n) ∈
      (Interval.point (diagonalBlock fun _ : Fin n => (one : 𝕋))).construct := by
    have h := Interval.mem_point (diagonalBlock fun _ : Fin n => (one : 𝕋))
    convert h using 1
    funext i j
    rw [realImage_mat, toRealMat, toReal_diagonalBlock]
    simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]
  have h := Zonotope.mtimesIntervalMat_outer _ Z
    (Set.mem_biUnion (Interval.smul_outer h₁ h₂ _ hone) ⟨v, hv, rfl⟩)
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact h

/-- A point of the interval matrix applied to a point of the zonotope. -/
theorem aux_absErrFloat_mulVec_mem {IM : Interval (Mat 𝕋 n n)} {Z : Zonotope (Vec 𝕋 n)}
    {M : Mat ℝ n n} {v : Vec ℝ n} (hM : M ∈ IM.construct) (hv : v ∈ Z.construct) :
    M *ᵥ v ∈ (Zonotope.mtimesIntervalMat IM Z).construct :=
  Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hM ⟨v, hv, rfl⟩)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13] at floats: `x(t) − y(t) ∈ E` for a run from `x₀ ∈ R₀` with inputs in `U`,
`t ∈ [0, tmax]`, `η ≥ 1`, `th ≥ 0`, under the float test on `‖tmax A‖`. -/
theorem GuardMap.abstractionErrorFloat_outer (A : Mat 𝕋 n n)
    (U R₀ : Zonotope (Vec 𝕋 n)) {th tmax : 𝕋}
    {t : ℝ} {η : ℕ} (hη : 1 ≤ η) (ht : t ∈ Set.Icc 0 (toReal tmax)) (hth : 0 ≤ toReal th)
    (hnrm : le (MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point A)))
      (half (nsmulDown (η + 2) one)) = true)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct) (hU : U.construct.Nonempty) {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ U.construct)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t)))
    : -- --- CONCL ---
    exp (t • toRealMat A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat A) *ᵥ u s)
        - GuardMap.sdcFlow (toRealMat A) (GuardMap.sdcInput (toRealMat A) (toRealVec U.c)
          (toReal th) η (toRealVec R₀.c)) x₀ t
      ∈ (GuardMap.abstractionErrorFloat A U R₀ th tmax η).construct := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
  set Ar : Mat ℝ n n := toRealMat A with hAr
  set nrm := MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point A)) with hnrmdef
  set ε := Float.MatExp.expRemainderBound nrm (k + 1) with hεdef
  -- the float test, read as the margin `nrm/(η + 2) ≤ 1/2`
  have hnn : 0 ≤ toReal nrm := by
    rw [hnrmdef, MatExp.normUpperBound, toReal_maximum, toReal_zero]
    exact le_max_left _ _
  have hmargin : toReal nrm / (((k + 1 : ℕ) : ℝ) + 2) ≤ 1 / 2 := by
    have h1 := toReal_le_of_le hnrm
    rw [toReal_half] at h1
    have h2 := nsmulDown_le (k + 1 + 2) (one : 𝕋)
    rw [toReal_one, mul_one] at h2
    rw [div_le_iff₀ (by positivity)]
    push_cast at h2 ⊢
    linarith
  have hnormA : ‖toReal tmax • Ar‖ ≤ toReal nrm :=
    MatExp.norm_smul_le_normUpperBound _ tmax (Interval.mem_point A)
  -- every remainder on `[0, tmax]` is within `ε` entrywise
  have hW : ∀ τ ∈ Set.Icc 0 (toReal tmax), ∀ j l,
      |(exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (k + 1)) j l| ≤ toReal ε := by
    intro τ hτ j l
    have hτn : ‖τ • Ar‖ ≤ toReal nrm := by
      refine le_trans ?_ hnormA
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ.1,
        abs_of_nonneg (hτ.1.trans hτ.2)]
      exact mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
    have hlt : ‖τ • Ar‖ / (((k + 1 : ℕ) : ℝ) + 2) < 1 := by
      have h := div_le_div_of_nonneg_right hτn (by positivity : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 2)
      linarith
    calc |(exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (k + 1)) j l|
        ≤ ‖exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (k + 1)‖ := Real.abs_entry_le_norm _ j l
      _ ≤ Real.MatExp.expRemainderBound (τ • Ar) (k + 1) := Real.norm_exp_sub_expTaylor_le _ _ hlt
      _ ≤ toReal ε := Float.MatExp.expRemainderBound_le (k + 1) hτn hnn hmargin
  have hε0 : 0 ≤ toReal ε :=
    (Real.MatExp.expRemainderBound_nonneg (x := (0 : Mat ℝ n n)) (k + 1) (by simp)).trans
      (Float.MatExp.expRemainderBound_le (k + 1) (by simpa using hnn) hnn hmargin)
  -- `Ê = [−ε, ε]` holds every matrix within `ε`, and `Ê tmax U` every `tmax M v`
  set What : Interval (Mat 𝕋 n n) := ⟨fun _ _ => neg ε, fun _ _ => ε⟩ with hWhat
  have hWmem : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ toReal ε) → M ∈ What.construct :=
    fun M hM => Interval.mem_mat_iff.mpr fun j l => by
      show toReal (neg ε) ≤ M j l ∧ M j l ≤ toReal ε
      rw [toReal_neg]
      exact abs_le.mp (hM j l)
  -- `Ê tmax U` holds `tmax M v` and, through the zero matrix, the origin
  have hS : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ (fun _ _ => toReal ε : Mat ℝ n n) j l) →
      ∀ v ∈ U.construct, toReal tmax • (M *ᵥ v) ∈
        (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax What) U).construct :=
    fun M hM v hv => by
      rw [← Matrix.smul_mulVec]
      exact aux_absErrFloat_mulVec_mem (Interval.smul_outer le_rfl le_rfl _ (hWmem M hM)) hv
  have hS0 : (0 : Vec ℝ n) ∈
      (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax What) U).construct := by
    obtain ⟨v, hv⟩ := hU
    simpa using hS 0 (fun j l => by simpa using hε0) v hv
  obtain ⟨w, hw, ρ, hρ, hid⟩ := GuardMap.abstractionError_decomp Ar
    (Zonotope.convex_construct U) (Zonotope.isCompact_construct U).isClosed
    (Zonotope.isCompact_construct U).isBounded hU (Zonotope.convex_construct _)
    (Zonotope.isCompact_construct _).isClosed (Zonotope.isCompact_construct _).isBounded hS0
    (toRealVec U.c) (toRealVec R₀.c) (toReal th) ht (fun _ _ => toReal ε) hW hS x₀ hu hmeas
  -- the point is `t(v₁ + v₂ + v₃) + R x₀ + ρ`
  rw [hid]
  -- the bounds every coefficient needs
  have ht0 := ht.1
  have htm := ht.2
  have hM : ∀ i m : ℕ, ((Nat.factorial (m + 2) : ℝ)⁻¹) • Ar ^ i ∈ (Interval.smul
      (MatExp.invFactorialBounds (m + 2)).inf (MatExp.invFactorialBounds (m + 2)).sup
      (Interval.matPow (Interval.point A) i)).construct := fun i m =>
    Interval.smul_outer (MatExp.invFactorialBounds_mem (m + 2)).1
      (MatExp.invFactorialBounds_mem (m + 2)).2 _
      (Interval.matPow_outer _ (Interval.mem_point A) i)
  have htHi : ∀ m : ℕ, t ^ (m + 1) ≤ toReal (powUp tmax (m + 1)) := fun m => le_powUp ht0 htm _
  have hthLo : ∀ m : ℕ, toReal (powDown th (m + 1)) ≤ toReal th ^ (m + 1) := fun m =>
    powDown_le hth le_rfl _
  have hthHi : ∀ m : ℕ, toReal th ^ (m + 1) ≤ toReal (powUp th (m + 1)) := fun m =>
    le_powUp hth le_rfl _
  -- the memberships, part by part, `ρ` already in `Ê tmax U`
  simp only [GuardMap.abstractionErrorFloat, Nat.add_sub_cancel]
  refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _
    (Set.add_mem_add ?_ ?_)) hρ)
  · -- `t(v₁ + v₂ + v₃)`, `t ∈ [0, tmax]`
    refine aux_absErrFloat_smul_mem (by rw [toReal_zero]; exact ht0) htm ?_
    refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _
      (Set.add_mem_add ?_ ?_)) ?_)
    · -- `err₁`: `(Aᵐ⁺²/(m + 2)!)(tᵐ⁺¹x₀ − thᵐ⁺¹ξ)`
      refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => aux_absErrFloat_mulVec_mem (hM _ m) ?_
      refine Zonotope.plus_outer _ _ (Set.add_mem_add
        (aux_absErrFloat_smul_mem (by rw [toReal_zero]; positivity) (htHi m) hx₀) ?_)
      refine Interval.zonotope_contains _ fun i => ?_
      have h := Interval.mul_between_corners (y := -(toReal th ^ (m + 1)))
        (x := toReal (R₀.c i)) (a := neg (powUp th (m + 1))) (b := neg (powDown th (m + 1)))
        (by rw [toReal_neg]; linarith [hthHi m]) (by rw [toReal_neg]; linarith [hthLo m])
        le_rfl le_rfl
      exact h
    · -- `err₂`: `((tᵐ⁺¹ − thᵐ⁺¹) Aᵐ⁺¹/(m + 2)!) u_c`
      refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => aux_absErrFloat_mulVec_mem
        (Interval.smul_outer ?_ ?_ _ (hM (m + 1) m)) ?_
      · rw [toReal_neg]
        linarith [hthHi m, pow_nonneg ht0 (m + 1)]
      · have h := sub_le_subUp (powUp tmax (m + 1)) (powDown th (m + 1))
        linarith [htHi m, hthLo m]
      · rw [Zonotope.construct_point]
        exact Set.mem_singleton _
    · -- `err₃`: `(w₀ − u_c) + ∑ (tᵐ⁺¹ Aᵐ⁺¹/(m + 2)!)(wₘ₊₁ − u_c)`
      refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.sub_center_mem_recenter (hw 0))
        (Zonotope.sum_mem_sumTerms _ _ _ fun m _ => aux_absErrFloat_mulVec_mem
          (Interval.smul_outer (by rw [toReal_zero]; positivity) (htHi m) _ (hM (m + 1) m))
          (Zonotope.sub_center_mem_recenter (hw (m + 1)))))
  · -- `R(t)x₀ ∈ Ê R₀`
    exact aux_absErrFloat_mulVec_mem (hWmem _ (hW t ht)) hx₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
