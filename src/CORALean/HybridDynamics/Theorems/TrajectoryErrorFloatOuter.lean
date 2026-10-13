module

public import CORALean.HybridDynamics.Operations.TrajectoryErrorFloat
public import CORALean.HybridDynamics.Theorems.AbstractionErrorDecomp
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PowHiLe
public import CORALean.ContSet.Interval.Float.Theorems.PowLoLe
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.Convex
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.SumTermsMem

@[expose] public section

/-!
# The float `E_err` encloses the error between the linear solution and the constant-derivative one

`LinearSys.trajectoryError_outer` at floats: for `t ∈ [tmin, tmax]`, `0 ≤ tmin`, `x₀ ∈ R₀` and
`η ≥ 1`, the solution `e^{At}x₀ + Γ(t)u` of `ẋ = Ax + u` minus the state-dependent constant flow
`x₀ + (Ax₀ + b)t`, `b` the exact `GuardMap.sdcInput` at `tc` and the stored centre of `R₀`, is
a point of the float `E_err` whenever `LinearSys.trajectoryErrorFloat` returns one, that is
whenever the float bound of `‖tmax A‖` passes `(η + 2)/2`. At `f₁ = f₂`, as the exact theorem.

The constant input is a measurable input with values in the point zonotope of `u`, so
`GuardMap.abstractionError_decomp` (with `th = tc`) gives the point as `t(v₁ + v₂) + R x₀ + ρ`,
its third part vanishing; `Γ(t)u` is the integral by `expIntegral_mulVec`. Each part is a point
of its float set: `tᵐ⁺¹x₀ − tcᵐ⁺¹ξ = tᵐ⁺¹(x₀ − ξ) + (tᵐ⁺¹ − tcᵐ⁺¹)ξ`, the coefficients in their
intervals (`matPow_outer`, `invFactorialBounds_mem`, directed powers and differences), `R` and
the remainder `ρ` within `Ê` by `norm_exp_sub_expTaylor_le` and the float bound.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
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
theorem aux_trajErrFloat_smul_mem {a b : 𝕋} {s : ℝ} (h₁ : toReal a ≤ s) (h₂ : s ≤ toReal b)
    {Z : Zonotope (Vec 𝕋 n)} {v : Vec ℝ n} (hv : v ∈ Z.construct) :
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
theorem aux_trajErrFloat_mulVec_mem {IM : Interval (Mat 𝕋 n n)} {Z : Zonotope (Vec 𝕋 n)}
    {M : Mat ℝ n n} {v : Vec ℝ n} (hM : M ∈ IM.construct) (hv : v ∈ Z.construct) :
    M *ᵥ v ∈ (Zonotope.mtimesIntervalMat IM Z).construct :=
  Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hM ⟨v, hv, rfl⟩)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13] at floats: `x(t) − y(t) ∈ E_err` for `x₀ ∈ R₀`, `t ∈ [tmin, tmax]`,
`0 ≤ tmin`, `η + 1 ≥ 1`, whenever the float `E_err` is returned. -/
theorem LinearSys.trajectoryErrorFloat_outer (sys : LinearSys 𝕋 n) (f u : Vec 𝕋 n)
    (R₀ : Zonotope (Vec 𝕋 n)) {tmin tmax tc : 𝕋} (hmin : 0 ≤ toReal tmin) (η : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (toReal tmin) (toReal tmax)) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct)
    {E : Zonotope (Vec 𝕋 n)}
    (hE : sys.trajectoryErrorFloat f f u R₀ tmin tmax tc (η + 1) = some E) :
    exp (t • toRealMat sys.A) *ᵥ x₀
        + Real.MatExp.expIntegral (toRealMat sys.A) t *ᵥ toRealVec u
        - GuardMap.sdcFlow (toRealMat sys.A) (GuardMap.sdcInput (toRealMat sys.A) (toRealVec u)
          (toReal tc) (η + 1) (toRealVec R₀.c)) x₀ t
      ∈ E.construct := by -- --- PROOF ---
  set A := sys.A with hAdef
  set Ar : Mat ℝ n n := toRealMat A with hAr
  set nrm := MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point A)) with hnrmdef
  set ε := Float.MatExp.expRemainderBound nrm (η + 1) with hεdef
  have ht0 : 0 ≤ t := hmin.trans ht.1
  have htI : t ∈ Set.Icc 0 (toReal tmax) := ⟨ht0, ht.2⟩
  -- the float test passed, and `E` is the returned set
  simp only [LinearSys.trajectoryErrorFloat] at hE
  split_ifs at hE with hnrm
  obtain rfl := Option.some.inj hE
  -- the float test, read as the margin `nrm/(η + 3) ≤ 1/2`
  have hnn : 0 ≤ toReal nrm := by
    rw [hnrmdef, MatExp.normUpperBound, toReal_maximum, toReal_zero]
    exact le_max_left _ _
  have hmargin : toReal nrm / (((η + 1 : ℕ) : ℝ) + 2) ≤ 1 / 2 := by
    have h1 := toReal_le_of_le hnrm
    rw [toReal_half] at h1
    have h2 := nsmulDown_le (η + 1 + 2) (one : 𝕋)
    rw [toReal_one, mul_one] at h2
    rw [div_le_iff₀ (by positivity)]
    push_cast at h2 ⊢
    linarith
  have hnormA : ‖toReal tmax • Ar‖ ≤ toReal nrm :=
    MatExp.norm_smul_le_normUpperBound _ tmax (Interval.mem_point A)
  -- every remainder on `[0, tmax]` is within `ε` entrywise
  have hW : ∀ τ ∈ Set.Icc 0 (toReal tmax), ∀ j l,
      |(exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (η + 1)) j l| ≤ toReal ε := by
    intro τ hτ j l
    have hτn : ‖τ • Ar‖ ≤ toReal nrm := by
      refine le_trans ?_ hnormA
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ.1,
        abs_of_nonneg (hτ.1.trans hτ.2)]
      exact mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
    have hlt : ‖τ • Ar‖ / (((η + 1 : ℕ) : ℝ) + 2) < 1 := by
      have h := div_le_div_of_nonneg_right hτn (by positivity : (0:ℝ) ≤ ((η + 1 : ℕ) : ℝ) + 2)
      linarith
    calc |(exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (η + 1)) j l|
        ≤ ‖exp (τ • Ar) - Real.MatExp.expTaylor (τ • Ar) (η + 1)‖ :=
          Real.abs_entry_le_norm _ j l
      _ ≤ Real.MatExp.expRemainderBound (τ • Ar) (η + 1) :=
          Real.norm_exp_sub_expTaylor_le _ _ hlt
      _ ≤ toReal ε := Float.MatExp.expRemainderBound_le (η + 1) hτn hnn hmargin
  have hε0 : 0 ≤ toReal ε :=
    (Real.MatExp.expRemainderBound_nonneg (x := (0 : Mat ℝ n n)) (η + 1) (by simp)).trans
      (Float.MatExp.expRemainderBound_le (η + 1) (by simpa using hnn) hnn hmargin)
  -- `Ê = [−ε, ε]` holds every matrix within `ε`
  set What : Interval (Mat 𝕋 n n) := ⟨fun _ _ => neg ε, fun _ _ => ε⟩ with hWhat
  have hWmem : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ toReal ε) → M ∈ What.construct :=
    fun M hM => Interval.mem_mat_iff.mpr fun j l => by
      show toReal (neg ε) ≤ M j l ∧ M j l ≤ toReal ε
      rw [toReal_neg]
      exact abs_le.mp (hM j l)
  -- the constant input: the point zonotope of `u`
  set uR : Vec ℝ n := toRealVec u with huR
  have hupt : ∀ v, v ∈ (Zonotope.point u).construct ↔ v = uR := fun v => by
    rw [Zonotope.construct_point]
    exact Set.mem_singleton_iff
  have hU : (Zonotope.point u).construct.Nonempty := ⟨uR, (hupt uR).mpr rfl⟩
  -- `Ê tmax u` holds `tmax M u` and, through the zero matrix, the origin
  have hS : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ (fun _ _ => toReal ε : Mat ℝ n n) j l) →
      ∀ v ∈ (Zonotope.point u).construct, toReal tmax • (M *ᵥ v) ∈
        (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax What) (Zonotope.point u)).construct :=
    fun M hM v hv => by
      rw [← Matrix.smul_mulVec]
      exact aux_trajErrFloat_mulVec_mem (Interval.smul_outer le_rfl le_rfl _ (hWmem M hM)) hv
  have hS0 : (0 : Vec ℝ n) ∈ (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax What)
      (Zonotope.point u)).construct := by
    simpa using hS 0 (fun j l => by simpa using hε0) uR ((hupt uR).mpr rfl)
  -- the decomposition at the constant input, `th = tc`
  obtain ⟨w, hw, ρ, hρ, hid⟩ := GuardMap.abstractionError_decomp Ar
    (Zonotope.convex_construct (Zonotope.point u))
    (Zonotope.isCompact_construct (Zonotope.point u)).isClosed
    (Zonotope.isCompact_construct (Zonotope.point u)).isBounded hU (Zonotope.convex_construct _)
    (Zonotope.isCompact_construct _).isClosed (Zonotope.isCompact_construct _).isBounded hS0
    uR (toRealVec R₀.c) (toReal tc) htI (fun _ _ => toReal ε) hW hS x₀ (u := fun _ => uR)
    (fun _ _ => (hupt uR).mpr rfl) aestronglyMeasurable_const
  -- every average of the constant input is the input
  have hw' : ∀ i, w i = uR := fun i => (hupt _).mp (hw i)
  -- `Γ(t)u` is the integral of the constant input
  have hint : Real.MatExp.expIntegral Ar t *ᵥ uR
      = ∫ s in (0:ℝ)..t, exp ((t - s) • Ar) *ᵥ uR := by
    rw [Real.MatExp.expIntegral_mulVec _ _ ht0]
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
      (f := fun σ => exp (σ • Ar) *ᵥ uR) t
    simp only [sub_self, sub_zero] at h
    exact h.symm
  -- the point is `t(v₁ + v₂) + R x₀ + ρ`, with the flow correction `t(f − f) = 0` added
  rw [hint, hid]
  simp only [hw', sub_self, Matrix.mulVec_zero, Finset.sum_const_zero, add_zero]
  have hf0 : ∀ X : Vec ℝ n, ∀ S : Set (Vec ℝ n),
      X + t • (toRealVec f - toRealVec f) ∈ S → X ∈ S := fun X S h => by
    rwa [sub_self, smul_zero, add_zero] at h
  apply hf0
  -- the bounds every coefficient needs
  have hM : ∀ i m : ℕ, ((Nat.factorial (m + 2) : ℝ)⁻¹) • Ar ^ i ∈ (Interval.smul
      (MatExp.invFactorialBounds (m + 2)).1 (MatExp.invFactorialBounds (m + 2)).2
      (Interval.matPow (Interval.point A) i)).construct := fun i m =>
    Interval.smul_outer (MatExp.invFactorialBounds_mem (m + 2)).1
      (MatExp.invFactorialBounds_mem (m + 2)).2 _
      (Interval.matPow_outer _ (Interval.mem_point A) i)
  -- the powers of `t ∈ [tmin, tmax]` between the directed powers
  have htLo : ∀ m : ℕ, toReal (powDown tmin (m + 1)) ≤ t ^ (m + 1) := fun m =>
    powDown_le hmin ht.1 _
  have htHi : ∀ m : ℕ, t ^ (m + 1) ≤ toReal (powUp tmax (m + 1)) := fun m =>
    le_powUp ht0 ht.2 _
  -- and `tᵐ⁺¹ − tcᵐ⁺¹` between the directed differences, `tc` of either sign
  have hdLo : ∀ m : ℕ, toReal (subDown (powDown tmin (m + 1)) (Interval.powHi tc (m + 1)))
      ≤ t ^ (m + 1) - toReal tc ^ (m + 1) := fun m => by
    have h1 := subDown_le_sub (powDown tmin (m + 1)) (Interval.powHi tc (m + 1))
    have h2 := Interval.le_powHi tc (m + 1)
    linarith [htLo m]
  have hdHi : ∀ m : ℕ, t ^ (m + 1) - toReal tc ^ (m + 1)
      ≤ toReal (subUp (powUp tmax (m + 1)) (Interval.powLo tc (m + 1))) := fun m => by
    have h1 := sub_le_subUp (powUp tmax (m + 1)) (Interval.powLo tc (m + 1))
    have h2 := Interval.powLo_le tc (m + 1)
    linarith [htHi m]
  -- the points of `Y`, `x0zono` and `uzono`
  have hY : x₀ - toRealVec R₀.c ∈ R₀.recentre.construct := Zonotope.sub_centre_mem_recentre hx₀
  have hξ : toRealVec R₀.c ∈ (Zonotope.point R₀.c).construct := by
    rw [Zonotope.construct_point]
    exact Set.mem_singleton _
  have hu : uR ∈ (Zonotope.point u).construct := (hupt uR).mpr rfl
  -- the memberships, part by part, `ρ` already in `Ê tmax u`
  simp only [Nat.add_sub_cancel]
  refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _
    (Set.add_mem_add (Zonotope.plus_outer _ _ (Set.add_mem_add ?_ ?_)) hρ)) ?_)
  · -- `t(v₁ + v₂)`, `t ∈ [tmin, tmax]`
    refine aux_trajErrFloat_smul_mem ht.1 ht.2 (Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_)
      (Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_)))
    · -- `(Aᵐ⁺²/(m + 2)!)(tᵐ⁺¹(x₀ − ξ) + (tᵐ⁺¹ − tcᵐ⁺¹)ξ)`
      have heq : t ^ (m + 1) • x₀ + (-(toReal tc ^ (m + 1))) • toRealVec R₀.c
          = t ^ (m + 1) • (x₀ - toRealVec R₀.c)
            + (t ^ (m + 1) - toReal tc ^ (m + 1)) • toRealVec R₀.c := by module
      rw [heq]
      exact aux_trajErrFloat_mulVec_mem (hM _ m) (Zonotope.plus_outer _ _ (Set.add_mem_add
        (aux_trajErrFloat_smul_mem (htLo m) (htHi m) hY)
        (aux_trajErrFloat_smul_mem (hdLo m) (hdHi m) hξ)))
    · -- `(Aᵐ⁺¹/(m + 2)!)((tᵐ⁺¹ − tcᵐ⁺¹)u)`
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul]
      exact aux_trajErrFloat_mulVec_mem (hM (m + 1) m)
        (aux_trajErrFloat_smul_mem (hdLo m) (hdHi m) hu)
  · -- `R(t)x₀ ∈ Ê R₀`
    exact aux_trajErrFloat_mulVec_mem (hWmem _ (hW t htI)) hx₀
  · -- the flow correction, `t(f − f)` in `T` times the box of `f − f`
    refine aux_trajErrFloat_smul_mem ht.1 ht.2 (Interval.zonotope_contains _ fun i => ?_)
    exact ⟨subDown_le_sub (f i) (f i), sub_le_subUp (f i) (f i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
