module

public import CORALean.ContDynamics.NonlinearSys.Definitions.HasFixedPointConfinement
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachAdaptivePassFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrAdaptiveFloatMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.OneStepFloatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# One pass of CORA's adaptive step holds every run of the real system

The abstraction-error loop of `linReachAdaptivePassFloat` stops at an `error_adm` whose box holds
`VerrorDyn`, the remainder over `Rmax` (`abstrErrAdaptiveFloat_mem`), where `Rmax` is the window
of the linearized system with input `f(z✱) ⊕ B(U - u✱) ⊕ [-error_adm, error_adm]`. So on `Rmax`
the field less `A (x - x✱)` lies in that input, and every run dominated by it stays in `Rmax`
(`oneStepFloat_outer`): that is the fixed point, and `HasFixedPointConfinement` turns it into
confinement of every run of `sys` in `Rmax`. There the field less its linear part lies in
`f(z✱) ⊕ B(U - u✱) ⊕ VerrorDyn`, the input of the pass's final linear step, and
`oneStepFloat_outer` places the run in its window and at its end.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `κ` – tensor order
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the admissible error
* `redFactor` – reduction factor
* `p` – square root precision
* `fuel` – iteration bound
* `R` – start zonotope
* `errorAdm` – initial admissible error
* `step` – linear step

## Hypotheses
* `h` – model encloses system
* `hfix` – the abstraction error's fixed point confines the runs

## Conclusion
* a successful pass encloses every run over its window and at its end
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- `f(x, u) - A(x - x✱)` is in `f(z✱) ⊕ B(U - u✱) ⊕ L` once the remainder is in `L`. -/
private theorem aux_pass_input {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) {U : Zonotope (Vec 𝕋 m)}
    {L : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n} {u : Vec ℝ m} (hu : u ∈ U.toSet)
    (hL : sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
      (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c)) ∈ L.toSet)
    : -- --- CONCL ---
    sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
      (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)) ⊞
          L).toSet := by -- --- PROOF ---
  set us := toRealVec U.c
  have hf₀ : sys.f (toRealVec xs) us ∈ (fm.f (Interval.point xs) (Interval.point U.c)).toSet :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  have hBu : Scalar.toRealMat B *ᵥ (u - us) ∈ toSet
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
      (Recenter.recenter U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion (Set.mem_singleton _)
      (Set.mem_image_of_mem _ (Zonotope.sub_center_mem_recenter hu)))
  have hsplit : sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      = (sys.f (toRealVec xs) us + Scalar.toRealMat B *ᵥ (u - us))
        + (sys.f x u - (sys.f (toRealVec xs) us + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
          + Scalar.toRealMat B *ᵥ (u - us))) := by abel
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Interval.zonotope_contains _ hf₀) hBu)) hL)

omit [ToRat 𝕋] in
/-- A zonotope whose box is within `e` in magnitude lies in the zonotope of `[-e, e]`. -/
private theorem aux_pass_box {V : Zonotope (Vec 𝕋 n)} {e : Vec 𝕋 n}
    (hle : ∀ i, le (V.interval.normMag i) (e i) = true) : -- --- CONCL ---
    V.toSet ⊆ (⟨-e, e⟩ : Interval (Vec 𝕋 n)).zonotope.toSet := by -- --- PROOF ---
  intro v hv
  refine Interval.zonotope_contains _ fun i => ?_
  obtain ⟨h1, h2⟩ := Zonotope.interval_contains V hv i
  have habs : |v i| ≤ toReal (V.interval.normMag i) := by
    rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs h1 h2
  have he := le_trans habs (toReal_le_of_le (hle i))
  show toReal ((-e) i) ≤ v i ∧ v i ≤ toReal (e i)
  rw [show (-e) i = neg (e i) from rfl, toReal_neg]
  exact ⟨by linarith [neg_abs_le (v i)], le_trans (le_abs_self _) he⟩

omit [ToRat 𝕋] in
/-- What the abstraction-error loop returns: `Rmax` is the window of a linear step at some
`error_adm` whose box holds `VerrorDyn`, the abstraction error over `Rmax`. -/
private theorem aux_pass_loop {fm : NonlinearSys.FloatHessModel 𝕋 n m} [ToRat 𝕋] {κ : ℕ}
    {A : Mat 𝕋 n n} {B : Mat 𝕋 n m} {xs : Vec 𝕋 n} {Vbase R : Zonotope (Vec 𝕋 n)}
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge redFactor : 𝕋}
    {p : ℕ} {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ (fuel c : ℕ) (perf : 𝕋) (e : Vec 𝕋 n) (res : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) ×
      Vec 𝕋 n), fm.step_abstrErrLoopAdaptive κ A B xs Vbase R U options enlarge redFactor p step
        fuel c perf e = some res →
      ∃ (e' : Vec 𝕋 n) (Rt : Zonotope (Vec 𝕋 n)), NonlinearSys.oneStepFloat A xs
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope) R options step =
            some (res.1, Rt) ∧
        res.2.1 = fm.abstrErrAdaptiveFloat κ A B xs res.1 U redFactor p ∧
        ∀ i, le (res.2.1.interval.normMag i) (e' i) = true := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro c perf e res hres; simp [NonlinearSys.FloatHessModel.step_abstrErrLoopAdaptive]
      at hres
  | succ fuel ih =>
    intro c perf e res hres
    unfold NonlinearSys.FloatHessModel.step_abstrErrLoopAdaptive at hres
    dsimp only at hres
    split at hres
    · exact absurd hres (by simp)
    · rename_i Rmax Rt' hstep
      split_ifs at hres with hconv hdiv
      · simp only [Option.some.injEq] at hres
        subst hres
        exact ⟨e, Rt', hstep, rfl, hconv⟩
      · exact ih _ _ _ _ hres


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful pass has a positive width, and every run of `sys` on `[0, Δt]` from `R` under
inputs in `U` is in `Rti` over the pass and in `Rtp` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachAdaptivePassFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (hfix : sys.HasFixedPointConfinement) {κ : ℕ} {U : Zonotope (Vec 𝕋 m)}
    {options : LinearSys.ReachFloatOptions 𝕋} {enlarge redFactor : 𝕋} {p fuel : ℕ}
    {R : Zonotope (Vec 𝕋 n)} {errorAdm : Vec 𝕋 n}
    {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ P ∈ fm.linReachAdaptivePassFloat κ U options enlarge redFactor p fuel R errorAdm step,
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U.toSet x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ P.Rti.toSet) ∧
          x (toReal options.Δt) ∈ P.Rtp.toSet := by -- --- PROOF ---
  intro P (hP : fm.linReachAdaptivePassFloat κ U options enlarge redFactor p fuel R errorAdm
    step = some P)
  unfold NonlinearSys.FloatHessModel.linReachAdaptivePassFloat at hP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hP
  obtain ⟨E, hE, S, hS, hpure⟩ := hP
  simp only [pure, Option.some.injEq] at hpure
  subst hpure
  set xs := (fm.toFloatModel.linPointFloat options.Δt R U).1
  set A := (fm.toFloatModel.linearizeFloat xs U.c).1
  set B := (fm.toFloatModel.linearizeFloat xs U.c).2
  set Vbase := (fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  -- the loop's fixed point: `Rmax` at some `error_adm` whose box holds `VerrorDyn`
  obtain ⟨e', Rt, hmax, hV, hle⟩ := aux_pass_loop _ _ _ _ E hE
  -- on `Rmax`, the field less `A (x - x✱)` is in the pass's final input, and in the loop's
  have hlin : ∀ {x : Vec ℝ n} {v : Vec ℝ m}, x ∈ E.1.toSet → v ∈ U.toSet →
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈ (Vbase ⊞ E.2.1).toSet :=
    fun hx hv => aux_pass_input h.toEncloses A B xs hv
      (hV ▸ h.abstrErrAdaptiveFloat_mem κ A B xs E.1 U redFactor p hx hv)
  have hlin' : ∀ x ∈ E.1.toSet, ∀ v ∈ U.toSet,
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
        (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet := by
    intro x hx v hv
    have hL := hV ▸ h.abstrErrAdaptiveFloat_mem κ A B xs E.1 U redFactor p hx hv
    exact aux_pass_input h.toEncloses A B xs hv (aux_pass_box (hV ▸ hle) hL)
  -- every run dominated by the loop's input stays in `Rmax`
  obtain ⟨hΔt, _⟩ := NonlinearSys.oneStepFloat_outer (sys := sys) _ _ hmax
  have hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
      (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
      sys'.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U' x' u' y' →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), sys'.f (x' t) (u' t)
        - Scalar.toRealMat A *ᵥ (x' t - toRealVec xs) ∈
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet) →
      ∀ t ∈ Set.Icc 0 (toReal options.Δt), x' t ∈ E.1.toSet :=
    fun m' sys' U' x' u' y' traj' hin =>
      ((NonlinearSys.oneStepFloat_outer (sys := sys') _ _ hmax).2 traj' hin).1
  obtain ⟨hΔt', hout⟩ := NonlinearSys.oneStepFloat_outer (sys := sys) _ _ hS
  refine ⟨hΔt, fun {x u y} traj => ?_⟩
  -- the fixed point confines the run, and the final step holds it
  have hconf := hfix (toReal options.Δt) R.toSet _ E.1.toSet U.toSet (Scalar.toRealMat A)
    (toRealVec xs) hdom hlin' x u y traj
  exact hout traj fun t ht => hlin (hconf t ht) (traj.input t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
