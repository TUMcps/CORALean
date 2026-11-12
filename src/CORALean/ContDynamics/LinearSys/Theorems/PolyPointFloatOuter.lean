module

public import CORALean.ContDynamics.LinearSys.Operations.PolyPointFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemAdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberExactPlus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceAdaptiveFiber
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `polyPointFloat` holds the state at the end of the step, at the start point's factors

A run of `ẋ = Ax + w`, from `x₀` at the factors `α` of `X₀`, whose input less a constant `vd` of
`Vs`'s dependent part (at the same `α`) stays in `V` and the independent part of `Vs`, is at `Δt`
the free motion `e^{AΔt} x₀`, the constant `vd`'s share `∫₀^Δt e^{As} ds vd`, the share of `ũ`, the
center of the rest, and the remainder, which is in `Ũ`'s input reach. The first two are the fibers
of `[e^{AΔt}] X₀` and `[∫₀^Δt e^{As} ds] Vs_dep` at the one `α` (`mtimesIntervalMat_fiber`), so
their sum is in the fiber of `exactPlusAlign`; the others are in `P̃(Δt)` and `P^R(Δt)`, the latter
with `Ũ` boxed to `n` generators (`reduce_outer`).

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `ζ` – reduction factor
* `p` – square root precision
* `V` – input zonotope
* `X₀` – start polynomial zonotope
* `Vs` – constant input, over `X₀`'s factors
* `R₀` – start set of the run
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `α` – factor values, by position
* `vd` – the dependent part of `Vs` at `α`

## Hypotheses
* `hΔt` – step length positive
* `traj` – signal is a canonical trajectory
* `hα` – the factors are in the unit box
* `hx` – the start is in the fiber of `X₀` at `α`
* `hvd` – the constant is in the fiber of `Vs`'s dependent part at `α`
* `hUb` – the input set is bounded
* `hUV` – every input less `vd` is in `V` and the independent part of `Vs`

## Conclusion
* the state at the end of the step is in `R`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet ContSetLike MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator-free zonotope at the stored zero holds `0`. -/
private theorem aux_pp_zero_mem_origin :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.toSet := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at the end of the step is in the end set. -/
theorem LinearSys.IsCanonicalTrajectory.polyPointFloat_outer {sys : LinearSys 𝕋 n} {Δt : 𝕋}
    {η : ℕ} {ζ : 𝕋} {p : ℕ} {V : Zonotope (Vec 𝕋 n)} {X₀ Vs : PolyZonotope (Vec 𝕋 n)}
    {R₀ U : Set (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} (hΔt : 0 < toReal Δt)
    (traj : sys.IsCanonicalTrajectory (S := ExactSet) (Set.Icc 0 (toReal Δt)) R₀ U x u)
    {α : ℕ → ℝ} (hα : ∀ k, |α k| ≤ 1) {vd : Vec ℝ n}
    (hx : x 0 ∈ X₀.fiber (fun k => α k)) (hvd : vd ∈ Vs.depPart.fiber (fun k => α k))
    (hUb : Bornology.IsBounded U)
    (hUV : ∀ z ∈ U, z - vd ∈ (V ⊞ Vs.indepZonotope).toSet) : -- --- CONCL ---
    ∀ R ∈ sys.polyPointFloat Δt η ζ p V X₀ Vs, x (toReal Δt) ∈ R.toSet := by -- --- PROOF ---
  intro R h
  rw [Option.mem_def] at h
  unfold LinearSys.polyPointFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨η', hη', s, hs, rfl⟩ := h
  have hexp := sys.exp_mem_expSquaringFloat (η := 16) (t := toReal Δt)
    (LinearSys.halvingsFloat_spec (by norm_num) s hs) le_rfl le_rfl
  have hη := (LinearSys.reachOrderFloat_spec _ hη').1
  set A := Scalar.toRealMat sys.A with hA
  set r := toReal Δt with hr
  set Vt := V ⊞ Vs.indepZonotope with hVt
  set ũ := Recenter.center Vt with hũ
  have hT : Set.Icc (0 : ℝ) r ⊆ Set.Icc 0 r := subset_rfl
  have hr0 : 0 ≤ r := hΔt.le
  -- the integral equation, and the input less the constant `ũ + vd`
  have hvoc := traj.variation_of_constants hT le_rfl hr0 hUb
  rw [sub_zero] at hvoc
  have hmeas := traj.aestronglyMeasurable_input hT
  -- the input less the constant is in `Ũ`, so its solution is in the input reach
  have hmem₀ : ∀ s ∈ Set.Icc (0 : ℝ) r, u s - vd - ũ ∈ toSet (Recenter.recenter Vt) :=
    fun s hs => Recenter.sub_center_mem_recenter (hUV _ (traj.input s hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - vd - ũ) (volume.restrict (Set.Icc 0 r)) :=
    (hmeas.sub aestronglyMeasurable_const).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := r) (S := ExactSet)
    (U := ({vd + ũ} : Set (Vec ℝ n))) hr0 Bornology.isBounded_singleton
    (fun _ _ => Set.mem_singleton _) aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := r) (S := 𝒵[𝕋])
    (U := Recenter.recenter Vt) hr0
    (CompactSet.isBounded_toSet (Recenter.recenter Vt)) hmem₀ hmeas₀
  -- the solution splits into the constant input's share and the rest
  have hsum : (∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ u s)
      = (∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ (vd + ũ))
        + ∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ (u s - vd - ũ) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add]
    have hu : vd + ũ + (u s - vd - ũ) = u s := by abel
    rw [hu]
  have hconst := Real.MatExp.expIntegral_constInput A (vd + ũ) hr0
  have hrest : (∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ (u s - vd - ũ))
      ∈ sys.inputReach (S := 𝒵[𝕋]) (Recenter.recenter Vt) r := by
    refine ⟨fun s => u s - vd - ũ, hmem₀, hmeas₀, ?_⟩
    rfl
  -- the pieces, one in each summand
  have hadm := hη
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hadm.1
  have hpt : ũ ∈ (Interval.point Vt.c).zonotope.toSet :=
    Interval.zonotope_contains _ (Interval.mem_point Vt.c)
  have hPu : Real.MatExp.expIntegral A r *ᵥ ũ ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
      (MatExp.adaptiveIntegral (Interval.point sys.A) Δt (m + 2))
      (Interval.point Vt.c).zonotope).toSet :=
    (Set.subset_biUnion_of_mem (u := fun M => (M *ᵥ ·) '' (Interval.point Vt.c).zonotope.toSet)
      (sys.expIntegral_mem_adaptiveIntegralFloat hr0 hadm)).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])
        (MatExp.adaptiveIntegral (Interval.point sys.A) Δt (m + 2))
        (Interval.point Vt.c).zonotope) ⟨ũ, hpt, rfl⟩
  -- (the series runs on `Ũ` boxed to `n` generators, a superset of `Ũ`)
  have hbox : (∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ (u s - vd - ũ))
      ∈ sys.inputReach (S := 𝒵[𝕋]) (Zonotope.reduce (Recenter.recenter Vt) 1) r := by
    obtain ⟨w, hw, hm, he⟩ := hrest
    exact ⟨w, fun s hs => Zonotope.reduce_outer _ 1 (hw s hs), hm, he⟩
  have hPU := Zonotope.reduceAdaptive_outer _ ζ p
    (sys.inputReach_subset_inputSolutionFloat hΔt hadm _ hbox)
  -- the free motion and the constant `vd` at the one set of factors
  have ha : ∀ k : Fin X₀.p, |(fun k : Fin X₀.p => α k) k| ≤ 1 := fun k => hα k
  have heA := PolyZonotope.mtimesIntervalMat_fiber
    (sys.expSquaringFloat Δt Δt 16 s) X₀ (hexp) ha hx
  have hPs := PolyZonotope.mtimesIntervalMat_fiber
    (MatExp.adaptiveIntegral (Interval.point sys.A) Δt (m + 2)) Vs.depPart
    (sys.expIntegral_mem_adaptiveIntegralFloat hr0 hadm) (fun k => hα k) hvd
  have heR := PolyZonotope.reduceAdaptive_fiber _ ζ p (fun k => hα k) heA
  have hex := PolyZonotope.exactPlusAlign_fiber _ _ α heR hPs
  have hex' : exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ vd ∈
      (PolyZonotope.exactPlusAlign
        ((PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X₀).reduceAdaptive
          ζ p)
        (PolyZonotope.mtimesIntervalMat
          (MatExp.adaptiveIntegral (Interval.point sys.A) Δt (m + 2)) Vs.depPart)
        ).compactGens.toSet :=
    PolyZonotope.compactGens_outer _
      ((PolyZonotope.mem_toSet_iff_fiber _ _).mpr ⟨_, fun k => hα k, hex⟩)
  -- the end state is their sum with the two input shares
  have hend : x r = ((exp (r • A) *ᵥ x 0 + Real.MatExp.expIntegral A r *ᵥ vd)
      + Real.MatExp.expIntegral A r *ᵥ ũ)
        + ∫ s in (0 : ℝ)..r, exp ((r - s) • A) *ᵥ (u s - vd - ũ) := by
    rw [hvoc, hsum, hconst, Matrix.mulVec_add]
    abel
  rw [hend]
  exact Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hex'
      (Zonotope.ofIndep_outer _ hPu))) (Zonotope.ofIndep_outer _ hPU))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
