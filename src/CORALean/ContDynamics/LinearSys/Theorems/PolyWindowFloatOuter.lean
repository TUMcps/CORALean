module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.PolyWindowFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachRecenter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.NegIdentityMatMulVec
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `polyWindowFloat` holds every run, and every difference it spans, over the step

A run of `ẋ = Ax + u`, `u(t) ∈ V`, from a point of the polynomial zonotope `X₀` is at time `t` the
free motion `e^{At} x₀`, the constant `ũ`'s share, and the rest, which `sub_mem_inputReach_recenter`
places in `Ũ`'s input reach. The free motion is the straight line `(1 - t/Δt) x₀ + (t/Δt) e^{AΔt}
x₀` and `[F] x₀` (the correction matrix), each in its summand by `mtimesIntervalMat_outer`; the
constant's share is in `P̃^R([0, ũ])` and the rest in `P^R(Ũ)`. The same split with `e^{At} x₀ - x₀`
in place of `e^{At} x₀` gives the difference.

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `ζ` – reduction factor
* `p` – square root precision
* `V` – input zonotope
* `X₀` – start polynomial zonotope
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `t` – time

## Hypotheses
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `hUV` – input set lies in the zonotope
* `ht` – time within the step

## Conclusion
* the state lies in the window and its difference from the start in the differences
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet ContSetLike

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored negated identity is the point interval at `-1`. -/
private theorem aux_pw_negOne_mem_point : -- --- CONCL ---
    (-1 : Mat ℝ n n) ∈ (Interval.point (negIdentityMat 𝕋 n)).toSet := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n)
  have he : (RealImage.realImage (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n) : Mat ℝ n n) = -1 := by
    funext i j
    show toReal (if i = j then FloatOps.neg (FloatOps.one : 𝕋) else FloatOps.zero)
      = (-1 : Mat ℝ n n) i j
    by_cases hij : i = j
    · rw [if_pos hij, toReal_neg, toReal_one, hij]; simp
    · rw [if_neg hij, toReal_zero]; simp [Matrix.one_apply_ne hij]
  rwa [he] at h

/-- The generator-free zonotope at the stored zero holds `0`. -/
private theorem aux_pw_zero_mem_origin :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.toSet := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, Δt]` from `X₀` under inputs in `U ⊆ V` is, at every time of the step, in the
window, and differs from its start by a point of the differences. -/
theorem LinearSys.IsCanonicalTrajectory.polyWindowFloat_outer {sys : LinearSys 𝕋 n} {Δt : 𝕋}
    {η : ℕ} {ζ : 𝕋} {p : ℕ} {V : Zonotope (Vec 𝕋 n)} {X₀ : PolyZonotope (Vec 𝕋 n)}
    {U : Set (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} (hΔt : 0 < toReal Δt)
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) X₀.toSet U x u)
    (hUV : U ⊆ V.toSet) {t : ℝ} (ht : t ∈ Set.Icc 0 (toReal Δt)) : -- --- CONCL ---
    ∀ WD ∈ sys.polyWindowFloat Δt η ζ p V X₀,
      x t ∈ WD.1.toSet ∧ x t - x 0 ∈ WD.2.toSet := by -- --- PROOF ---
  rintro ⟨W, D⟩ h
  rw [Option.mem_def] at h
  unfold LinearSys.polyWindowFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨η', hη', s, hs, rfl, rfl⟩ := h
  have hexp := sys.exp_mem_expSquaringFloat (η := 16) (t := toReal Δt)
    (LinearSys.halvingsFloat_spec (by norm_num) s hs) le_rfl le_rfl
  have hη := (LinearSys.reachOrderFloat_spec _ hη').1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set ũ := Recenter.center V with hũ
  have hx0 : x 0 ∈ X₀.toSet := traj.init
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.toSet :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.toSet := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_pw_zero_mem_origin, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.toSet := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_pw_zero_mem_origin, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant's share by `t`, inside `P̃^R([0, ũ])`
  have hconst : Real.MatExp.expIntegral A t *ᵥ ũ
      ∈ (sys.inputSolutionFloat Δt (m + 2) seg).toSet :=
    sys.inputReach_subset_inputSolutionFloat hΔt hη seg
      (sys.inputReach_mono (CompactSet.isBounded_toSet seg) h0seg ht.1 ht.2
        ⟨fun _ => ũ, fun _ _ => hũseg, MeasureTheory.aestronglyMeasurable_const,
          (Real.MatExp.expIntegral_constInput A ũ ht.1).symm⟩)
  -- the rest of the input's share by `t`, inside `P^R(Ũ)`
  have hrest := sys.inputReach_subset_inputSolutionFloat hΔt hη _
    (sys.inputReach_mono (CompactSet.isBounded_toSet _) (Recenter.zero_mem_recenter V) ht.1
      ht.2 (traj.sub_mem_inputReach_recenter hUV ht))
  have hPuRz := Zonotope.reduceAdaptive_outer _ ζ p hconst
  have hPUz := Zonotope.reduceAdaptive_outer _ ζ p hrest
  have hPuR := Zonotope.ofIndep_outer _ hPuRz
  have hPU := Zonotope.ofIndep_outer _ hPUz
  -- the free motion's products with `X₀`
  have hl0 : 0 ≤ t / r := div_nonneg ht.1 hΔt.le
  have hl1 : t / r ≤ 1 := (div_le_one hΔt).mpr ht.2
  have hmt : ∀ {IM : Interval (Mat 𝕋 n n)} {M : Mat ℝ n n}, M ∈ IM.toSet →
      M *ᵥ x 0 ∈ (PolyZonotope.mtimesIntervalMat IM X₀).toSet := fun {IM M} hM =>
    PolyZonotope.mtimesIntervalMat_outer IM X₀ (Set.mem_biUnion hM (Set.mem_image_of_mem _ hx0))
  have hE : exp (r • A) *ᵥ x 0 ∈ (PolyZonotope.mtimesIntervalMat
      (sys.expSquaringFloat Δt Δt 16 s) X₀).toSet :=
    hmt (hexp)
  have hEI : (exp (r • A) - 1) *ᵥ x 0 ∈ (PolyZonotope.mtimesIntervalMat
      (Interval.matPlus (sys.expSquaringFloat Δt Δt 16 s)
        (Interval.point (negIdentityMat 𝕋 n))) X₀).toSet := by
    have hM := Interval.matPlus_outer _ _ (hexp)
      aux_pw_negOne_mem_point
    rw [← sub_eq_add_neg] at hM
    exact hmt hM
  have hF : (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x 0 ∈
      (PolyZonotope.mtimesIntervalMat (MatExp.intervalCorrectionMatrix (Interval.point sys.A)
        Δt (m + 2)) X₀).toSet :=
    hmt (MatExp.expDiff_mem_intervalCorrectionMatrix _ hΔt hη.2 (Interval.mem_point sys.A)
      ht.1 ht.2)
  -- the run is its free motion, the constant's share and the rest
  obtain ⟨y, hy⟩ : ∃ y, y = x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ) :=
    ⟨_, rfl⟩
  rw [← hy] at hPU hPUz
  -- the run, as a split into the pieces
  have hsplit : x t = (exp (t • A) *ᵥ x 0) + Real.MatExp.expIntegral A t *ᵥ ũ + y := by
    rw [hy]; abel
  have hsplit' : x t - x 0 = (exp (t • A) *ᵥ x 0 - x 0)
      + (Real.MatExp.expIntegral A t *ᵥ ũ + y) := by
    rw [hy]; abel
  -- the free motion is the straight line between its ends plus the curvature
  have hdecomp : exp (t • A) *ᵥ x 0
      = ((1 - t / r) • x 0 + (t / r) • (exp (r • A) *ᵥ x 0))
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x 0 := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  have hddecomp : exp (t • A) *ᵥ x 0 - x 0
      = (1 - t / r) • (0 : Vec ℝ n) + (t / r) • ((exp (r • A) - 1) *ᵥ x 0)
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x 0 := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, smul_zero, zero_add,
      smul_sub]
    abel
  -- the line is in the combination of the start set and its image
  have hcomb : ((1 - t / r) • x 0 + (t / r) • (exp (r • A) *ᵥ x 0)) ∈ (LinComb.linComb X₀
      (PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X₀)).toSet := by
    refine LinComb.linComb_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ ?_
    exact ⟨x 0, hx0, _, hE, 1 - t / r, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  have hdcomb : ((1 - t / r) • (0 : Vec ℝ n) + (t / r) • ((exp (r • A) - 1) *ᵥ x 0)) ∈
      (LinComb.linComb (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.ofIndep
        (PolyZonotope.mtimesIntervalMat (Interval.matPlus (sys.expSquaringFloat Δt Δt 16 s)
          (Interval.point (negIdentityMat 𝕋 n))) X₀)).toSet := by
    refine LinComb.linComb_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ ?_
    exact ⟨0, Zonotope.ofIndep_outer _ aux_pw_zero_mem_origin, _, hEI,
      1 - t / r, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- the state and the difference are each a sum of the pieces
  refine ⟨?_, ?_⟩
  · rw [hsplit, hdecomp]
    exact Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
        (PolyZonotope.reduceAdaptive_outer _ ζ p
          (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hcomb hF)))
        hPuR)) hPU)
  · rw [hsplit', hddecomp]
    exact Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
      (PolyZonotope.reduceAdaptive_outer _ ζ p
        (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hdcomb hF)))
      (Zonotope.ofIndep_outer _ (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add hPuRz hPUz))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
