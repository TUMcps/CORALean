module

public import CORALean.ContDynamics.LinearSys.Theorems.CanonicalFloatInput
public import CORALean.ContDynamics.LinearSys.Theorems.PolyPointFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.PolyWindowFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Definitions.HasTrackedStaticError
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyAdaptivePassFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolyAdaptiveFloatMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.FloatModelEnclosesBaseMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.FloatModelEnclosesMemOfFixedPoint
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeSub
public import CORALean.ContDynamics.NonlinearSys.Theorems.PrecompStatErrorAdaptiveFloatMemStat
public import CORALean.ContDynamics.NonlinearSys.Theorems.PrecompStatErrorAdaptiveFloatMemZdelta
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.PolyZonotope.Float.Theorems.DepPointMemFiberDepPart
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SubDepPointMemIndepZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem

@[expose] public section

/-!
# One pass of CORA's poly-adaptive step holds every run of the real system

The loop of `linReachPolyAdaptivePassFloat` stops at an `error_adm` whose box holds
`VerrorDyn ⊕ Vstat`, the remainder over `Rmax` (`abstrErrPolyAdaptiveFloat_mem`). So the field less
`A (x - x✱)` lies in the window's input on `x✱ + Rdelta + Rdiff`, and every run dominated by it
stays there (`polyWindowFloat_outer`): this is the fixed point, which
`Encloses.mem_of_fixedPoint` turns into confinement of every run of `sys` in `x✱ + Rdelta + Rdiff`,
a compact set inside the zonotope `Rmax`, over which the field is Lipschitz by `Encloses`. The
run's differences are then in `Rdiff`, its static error is a point of `Vstat` at the factors of its
start point (`HasTrackedStaticError`), and `polyPointFloat_outer` puts the run's end in the end set.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the admissible error
* `redFactor` – reduction factor
* `p` – square root precision
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `errorAdm` – initial admissible error

## Hypotheses
* `h` – model encloses system
* `htrack` – the static error follows the factors of the start set

## Conclusion
* a successful pass has a positive width and encloses every run over its window and at its end
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `f(x, u) - A(x - x✱) - s` is in `f(z✱) ⊕ B(U - u✱) ⊕ L` once the remainder less `s` is in `L`.
-/
private theorem aux_ppass_input {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) {U : Zonotope (Vec 𝕋 m)}
    {L : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n} {u : Vec ℝ m} {s : Vec ℝ n} (hu : u ∈ U.toSet)
    (hL : sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c)
      + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c)) - s
      ∈ L.toSet) : -- --- CONCL ---
    sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) - s ∈
      (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)) ⊞
          L).toSet := by -- --- PROOF ---
  set us := toRealVec U.c
  -- the field at the linearization point and the input share
  have hf₀ : sys.f (toRealVec xs) us ∈ (fm.f (Interval.point xs) (Interval.point U.c)).toSet :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  have hBu : Scalar.toRealMat B *ᵥ (u - us) ∈
      toSet (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion (Set.mem_singleton _)
        (Set.mem_image_of_mem _ (Zonotope.sub_center_mem_recenter hu)))
  -- the field less its linear part is those two plus the remainder less `s`
  have hsplit : sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) - s
      = (sys.f (toRealVec xs) us + Scalar.toRealMat B *ᵥ (u - us))
        + (sys.f x u - (sys.f (toRealVec xs) us + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
          + Scalar.toRealMat B *ᵥ (u - us)) - s) := by abel
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Interval.zonotope_contains _ hf₀) hBu)) hL)

/-- A zonotope whose box is within `e` in magnitude lies in the zonotope of `[-e, e]`. -/
private theorem aux_ppass_box {V : Zonotope (Vec 𝕋 n)} {e : Vec 𝕋 n}
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

/-- The generator-free zonotope at `v` holds `v`. -/
private theorem aux_ppass_mem_pt {k : ℕ} (v : Vec 𝕋 k) : -- --- CONCL ---
    toRealVec v ∈ (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 k)).toSet := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩

/-- What the abstraction-error loop returns: a window of the linear step at some `error_adm`, the
differences `Rdiff` of which give the region `VerrorDyn` is read over, and a box of `VerrorDyn`
and `Vstat` within `error_adm`. -/
private theorem aux_ppass_loop {fm : NonlinearSys.FloatHessModel 𝕋 n m} {A : Mat 𝕋 n n}
    {B : Mat 𝕋 n m} {xs : Vec 𝕋 n} {Vbase : Zonotope (Vec 𝕋 n)}
    {Rdelta Vstat : PolyZonotope (Vec 𝕋 n)} {Zdelta : Zonotope (Vec 𝕋 (n + m))}
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge redFactor : 𝕋}
    {p : ℕ} : -- --- CONCL ---
    ∀ (fuel c : ℕ) (perf : 𝕋) (e : Vec 𝕋 n) (res : Zonotope (Vec 𝕋 n) × Vec 𝕋 n),
      fm.step_abstrErrLoopPolyAdaptive A B xs Vbase Rdelta Vstat Zdelta U options enlarge
        redFactor p fuel c perf e = some res →
      ∃ (e' : Vec 𝕋 n) (Wd Rdiff : PolyZonotope (Vec 𝕋 n)),
        (LinearSys.canonicalFloat A : LinearSys 𝕋 n).polyWindowFloat options.Δt
          options.η redFactor p (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope) Rdelta
            = some (Wd, Rdiff) ∧
        res.1 = fm.abstrErrPolyAdaptiveFloat A B xs ((Rdelta.zonotopeEven.materialise ⊞
          Rdiff.zonotopeEven.materialise) ⊞ (⟨0, xs, fun j => j.elim0,
            ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))).materialise Zdelta Rdiff U
              redFactor p ∧
        ∀ i, le ((res.1 ⊞ Vstat.zonotopeEven.materialise).interval.normMag i) (e' i)
          = true := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
    intro c perf e res hres
    unfold NonlinearSys.FloatHessModel.step_abstrErrLoopPolyAdaptive at hres
    exact absurd hres (by simp)
  | succ fuel ih =>
    intro c perf e res hres
    unfold NonlinearSys.FloatHessModel.step_abstrErrLoopPolyAdaptive at hres
    simp only [Option.bind_eq_some_iff] at hres
    obtain ⟨W, hwin, hres⟩ := hres
    split_ifs at hres with hconv hdiv
    · simp only [Option.some.injEq] at hres
      subst hres
      exact ⟨e, W.1, W.2, hwin, rfl, hconv⟩
    · exact ih _ _ _ _ hres


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful pass has a positive width, and every run of `sys` on `[0, Δt]` from `R` under
inputs in `U` is in `Rti` over the pass and in `Rtp` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachPolyAdaptivePassFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)}
    {options : LinearSys.ReachFloatOptions 𝕋} {enlarge redFactor : 𝕋} {p fuel : ℕ}
    {R : PolyZonotope (Vec 𝕋 n)} {errorAdm : Vec 𝕋 n}
    (htrack : fm.HasTrackedPassStaticError U options redFactor p R) : -- --- CONCL ---
    ∀ P ∈ fm.linReachPolyAdaptivePassFloat U options enlarge redFactor p fuel R errorAdm,
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U.toSet x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ P.Rti.toSet) ∧
          x (toReal options.Δt) ∈ P.Rtp.toSet := by -- --- PROOF ---
  intro P (hP : fm.linReachPolyAdaptivePassFloat U options enlarge redFactor p fuel R errorAdm =
    some P)
  have hlt : ltStrict (zero : 𝕋) options.Δt = true := by
    by_contra hc
    rw [Bool.not_eq_true] at hc
    simp [NonlinearSys.FloatHessModel.linReachPolyAdaptivePassFloat, hc] at hP
  have hΔt : 0 < toReal options.Δt := by
    have := toReal_lt_of_ltStrict hlt
    rwa [toReal_zero] at this
  -- unfold the pass, and name its parts
  unfold NonlinearSys.FloatHessModel.linReachPolyAdaptivePassFloat at hP
  simp only [hlt, if_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at hP
  obtain ⟨_, -, E, hE, W, hW, Rtp, hRtp, hpure⟩ := hP
  simp only [pure, Option.some.injEq] at hpure
  subst hpure
  set Rc : Zonotope (Vec 𝕋 n) := ⟨0, R.c, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
    with hRc
  set xs := (fm.toFloatModel.linPointFloat options.Δt Rc U).1 with hxs
  set A := (fm.toFloatModel.linearizeFloat xs U.c).1 with hA
  set B := (fm.toFloatModel.linearizeFloat xs U.c).2 with hB
  set Vbase := (fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U) with hVbase
  set Rdelta := R ⊞ (Interval.point (-xs)).zonotope.ofIndep with hRdelta
  set S := fm.precompStatErrorAdaptiveFloat xs U redFactor p Rdelta with hS
  refine ⟨hΔt, fun {x u y} traj => ?_⟩
  -- the loop's fixed point: the window at some `error_adm` whose box holds `VerrorDyn ⊕ Vstat`
  obtain ⟨e', Wd, Rdiff, hwin, hV, hle⟩ := aux_ppass_loop _ _ _ _ E hE
  set Vsz := S.1.zonotopeEven.materialise with hVsz
  set Verror := (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope with hVerror
  set pt0 : Zonotope (Vec 𝕋 n) :=
    ⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ with hpt0
  set Rmax := ((Rdelta.zonotopeEven.materialise ⊞ Rdiff.zonotopeEven.materialise) ⊞ pt0).materialise
    with hRmax
  -- the start set less `x✱`
  have hRd : ∀ x₀ ∈ R.toSet, x₀ - toRealVec xs ∈ Rdelta.toSet := by
    intro x₀ hx₀
    have hp := Zonotope.ofIndep_outer _ (Interval.zonotope_contains _
      (Interval.mem_point (α := Vec 𝕋 n) (-xs)))
    have hneg : RealImage.realImage (α := Vec 𝕋 n) (-xs) = -toRealVec xs := toRealVec_neg _
    rw [hneg] at hp
    have := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) R _ (Set.add_mem_add hx₀ hp)
    rwa [← sub_eq_add_neg] at this
  -- the region holds the start set and the differences
  have hK : ∀ {a d : Vec ℝ n}, a ∈ Rdelta.toSet → d ∈ Rdiff.toSet →
      toRealVec xs + a + d ∈ Rmax.toSet := by
    intro a d ha hd
    rw [hRmax, Zonotope.materialise_eq]
    have hm := Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ pt0 (Set.add_mem_add
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) Rdelta.zonotopeEven.materialise
        Rdiff.zonotopeEven.materialise (Set.add_mem_add
          (by rw [Zonotope.materialise_eq]; exact PolyZonotope.zonotopeEven_contains _ ha)
          (by rw [Zonotope.materialise_eq]; exact PolyZonotope.zonotopeEven_contains _ hd)))
      (aux_ppass_mem_pt xs))
    rwa [show toRealVec xs + a + d = a + d + toRealVec xs by abel]
  -- the remainder less the static error is in `VerrorDyn`, the static error in `Vsz`
  have hrem : ∀ {x : Vec ℝ n} {v : Vec ℝ m} {a d : Vec ℝ n}, x - toRealVec xs = a + d →
      a ∈ Rdelta.toSet → d ∈ Rdiff.toSet → v ∈ U.toSet →
      sys.f x v - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
        + Scalar.toRealMat B *ᵥ (v - toRealVec U.c))
        - (fun i => Fin.append a (v - toRealVec U.c) ⬝ᵥ (Scalar.toRealMat
          ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ
            Fin.append a (v - toRealVec U.c)) / 2) ∈ E.1.toSet := by
    intro x v a d hxd ha hd hv
    -- the state is in the region
    have hx : x ∈ Rmax.toSet := by
      have := hK ha hd
      rwa [show toRealVec xs + a + d = x by rw [add_assoc, ← hxd]; abel] at this
    have hμ : v - toRealVec U.c ∈ (Recenter.recenter U).toSet := Zonotope.sub_center_mem_recenter hv
    rw [hV]
    exact h.abstrErrPolyAdaptiveFloat_mem A B xs Rmax S.2 Rdiff U redFactor p hx hxd
      (fm.precompStatErrorAdaptiveFloat_mem_Zdelta xs U redFactor p Rdelta ha hμ) hd hv
  -- the static error at a start point and an input is in `Vstat`
  have hstat : ∀ {a : Vec ℝ n} {v : Vec ℝ m}, a ∈ Rdelta.toSet → v ∈ U.toSet →
      (fun i => Fin.append a (v - toRealVec U.c) ⬝ᵥ (Scalar.toRealMat
        ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ
          Fin.append a (v - toRealVec U.c)) / 2) ∈ Vsz.toSet := by
    intro a v ha hv
    rw [hVsz, Zonotope.materialise_eq]
    exact PolyZonotope.zonotopeEven_contains _ (fm.precompStatErrorAdaptiveFloat_mem_stat xs U
      redFactor p Rdelta ha (Zonotope.sub_center_mem_recenter hv))
  -- on the region, the field less `A (x - x✱)` is in the loop's input
  have hloop : ∀ {x : Vec ℝ n} {v : Vec ℝ m} {a d : Vec ℝ n}, x - toRealVec xs = a + d →
      a ∈ Rdelta.toSet → d ∈ Rdiff.toSet → v ∈ U.toSet →
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈ (Vbase ⊞ Verror).toSet := by
    intro x v a d hxd ha hd hv
    have hr := hrem hxd ha hd hv
    have hsum := Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) E.1 Vsz
      (Set.add_mem_add hr (hstat ha hv))
    rw [sub_add_cancel] at hsum
    have hL := aux_ppass_box hle hsum
    have hres := aux_ppass_input h.toEncloses A B xs (s := 0) hv (L := Verror)
      (by rw [sub_zero]; exact hL)
    rwa [sub_zero] at hres
  -- every run dominated by the loop's input stays in `x✱ + Rdelta + Rdiff`
  set K : Set (Vec ℝ n) :=
    {y | ∃ a ∈ Rdelta.toSet, ∃ d ∈ Rdiff.toSet, y = toRealVec xs + a + d} with hKdef
  have hlinK : ∀ y ∈ K, ∀ v ∈ U.toSet, sys.f y v - Scalar.toRealMat A *ᵥ (y - toRealVec xs)
      ∈ (Vbase ⊞ Verror).toSet := by
    rintro y ⟨a, ha, d, hd, rfl⟩ v hv
    exact hloop (by abel) ha hd hv
  have hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
      (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
      sys'.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U' x' u' y' →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), sys'.f (x' t) (u' t)
        - Scalar.toRealMat A *ᵥ (x' t - toRealVec xs) ∈ (Vbase ⊞ Verror).toSet) →
      ∀ t ∈ Set.Icc 0 (toReal options.Δt), x' t ∈ K := by
    intro m' sys' U' x' u' y' traj' hin t ht
    have ltraj := traj'.linearize_sub (lsys := (LinearSys.canonicalFloat A : LinearSys 𝕋 n))
      (xs := toRealVec xs) (X₀ := Rdelta.toSet) (V := (Vbase ⊞ Verror).toSet)
      measurableSet_Icc (hRd _ traj'.init) hin
    obtain ⟨-, hd⟩ := LinearSys.IsCanonicalTrajectory.polyWindowFloat_outer hΔt ltraj
      subset_rfl ht _ hwin
    refine ⟨x' 0 - toRealVec xs, hRd _ traj'.init, _, hd, ?_⟩
    abel
  -- the set `K` is compact, so closed, and inside the zonotope `Rmax`
  have hKc : IsClosed K := by
    have : K = (fun p : Vec ℝ n × Vec ℝ n => toRealVec xs + p.1 + p.2) '' (Rdelta.toSet ×ˢ
        Rdiff.toSet) := by
      ext y
      simp only [hKdef, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists]
      constructor
      · rintro ⟨a, ha, d, hd, rfl⟩
        exact ⟨a, d, ⟨ha, hd⟩, rfl⟩
      · rintro ⟨a, d, ⟨ha, hd⟩, rfl⟩
        exact ⟨a, ha, d, hd, rfl⟩
    rw [this]
    exact ((PolyZonotope.isCompact_toSet Rdelta).prod (PolyZonotope.isCompact_toSet Rdiff)).image
      (by fun_prop) |>.isClosed
  have hKR : K ⊆ Rmax.toSet := by
    rintro _ ⟨a, ha, d, hd, rfl⟩
    exact hK ha hd
  -- the loop's input set is bounded and nonempty
  have hVb : Bornology.IsBounded (Vbase ⊞ Verror).toSet := (Zonotope.isCompact_toSet _).isBounded
  have hVne : (Vbase ⊞ Verror).toSet.Nonempty := by
    have h0 : (0 : Vec ℝ n) ∈ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).toSet := fun i => by
      have h1 := toReal_le_of_le (hle i)
      have h2 : 0 ≤ toReal ((E.1 ⊞ Vsz).interval.normMag i) := by
        rw [Interval.normMag, toReal_maximum, toReal_absolute]
        exact le_max_of_le_left (abs_nonneg _)
      show toReal ((-e') i) ≤ 0 ∧ 0 ≤ toReal (e' i)
      rw [show (-e') i = neg (e' i) from rfl, toReal_neg]
      constructor <;> linarith
    exact ⟨_, Plus.plus_outer Vbase _ (Set.add_mem_add
      (h.toEncloses.base_mem B xs (traj.input 0 ⟨le_rfl, hΔt.le⟩))
      (Interval.zonotope_contains _ h0))⟩
  -- the fixed point confines the run
  have hconf := h.toEncloses.mem_of_fixedPoint (sys := sys) hΔt.le (K := K) Rmax
    (Scalar.toRealMat A) xs hVb hVne hKc hKR hdom hlinK traj
  have hw : ∀ t ∈ Set.Icc 0 (toReal options.Δt), sys.f (x t) (u t)
      - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ (Vbase ⊞ Verror).toSet :=
    fun t ht => hlinK _ (hconf t ht) _ (traj.input t ht)
  have lt1 := traj.linearize_sub (lsys := (LinearSys.canonicalFloat A : LinearSys 𝕋 n))
    (xs := toRealVec xs) (X₀ := Rdelta.toSet) (V := (Vbase ⊞ Verror).toSet)
    measurableSet_Icc (hRd _ traj.init) hw
  -- the run's differences are in `Rdiff`, so its remainder less the static error is in `VerrorDyn`
  have hdiff : ∀ t ∈ Set.Icc 0 (toReal options.Δt),
      x t - toRealVec xs - (x 0 - toRealVec xs) ∈ Rdiff.toSet := fun t ht =>
    (LinearSys.IsCanonicalTrajectory.polyWindowFloat_outer hΔt lt1 subset_rfl ht _ hwin).2
  -- the static error of the run's start point with its input at time `t`
  set statAt : ℝ → Vec ℝ n := fun t => fun i => Fin.append (x 0 - toRealVec xs)
    (u t - toRealVec U.c) ⬝ᵥ (Scalar.toRealMat
      ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ
        Fin.append (x 0 - toRealVec xs) (u t - toRealVec U.c)) / 2 with hstatAt
  -- the remainder at the run, less the static error at its start point, is in `VerrorDyn`
  have hrem_t : ∀ t ∈ Set.Icc 0 (toReal options.Δt), sys.f (x t) (u t) - (sys.f (toRealVec xs)
      (toRealVec U.c) + Scalar.toRealMat A *ᵥ (x t - toRealVec xs)
        + Scalar.toRealMat B *ᵥ (u t - toRealVec U.c))
      - statAt t ∈ E.1.toSet :=
    fun t ht => hrem (by abel) (hRd _ traj.init) (hdiff t ht) (traj.input t ht)
  have hstat_t : ∀ t ∈ Set.Icc 0 (toReal options.Δt), statAt t ∈ Vsz.toSet :=
    fun t ht => hstat (hRd _ traj.init) (traj.input t ht)
  -- the field less its static error is in the pass's input
  have hfield : ∀ t ∈ Set.Icc 0 (toReal options.Δt), sys.f (x t) (u t)
      - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) - statAt t ∈ (Vbase ⊞ E.1).toSet :=
    fun t ht => aux_ppass_input h.toEncloses A B xs (traj.input t ht) (hrem_t t ht)
  -- the window
  have hwf : ∀ t ∈ Set.Icc 0 (toReal options.Δt), sys.f (x t) (u t)
      - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ ((Vbase ⊞ E.1) ⊞ Vsz).toSet := by
    intro t ht
    have := Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ Vsz
      (Set.add_mem_add (hfield t ht) (hstat_t t ht))
    rwa [sub_add_cancel] at this
  have lt2 := traj.linearize_sub (lsys := (LinearSys.canonicalFloat A : LinearSys 𝕋 n))
    (xs := toRealVec xs) (X₀ := Rdelta.toSet) (V := ((Vbase ⊞ E.1) ⊞ Vsz).toSet)
    measurableSet_Icc (hRd _ traj.init) hwf
  have hpt : toRealVec xs ∈ (Interval.point xs).zonotope.ofIndep.toSet :=
    Zonotope.ofIndep_outer _ (Interval.zonotope_contains _ (Interval.mem_point xs))
  have hback : ∀ {Z : PolyZonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z - toRealVec xs ∈ Z.toSet →
      z ∈ (Z ⊞ (Interval.point xs).zonotope.ofIndep).toSet := fun {Z z} hz => by
    have := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) Z _ (Set.add_mem_add hz hpt)
    rwa [sub_add_cancel] at this
  refine ⟨fun t ht => ?_, ?_⟩
  · exact hback
      (LinearSys.IsCanonicalTrajectory.polyWindowFloat_outer hΔt lt2 subset_rfl ht _ hW).1
  · -- the end set: the start point's factors carry the static error
    obtain ⟨a₀, ha₀, hfib0⟩ := (PolyZonotope.mem_toSet_iff_fiber Rdelta _).mp (hRd _ traj.init)
    set α : ℕ → ℝ := fun k => if hk : k < Rdelta.p then a₀ ⟨k, hk⟩ else 0 with hα
    -- the factors, zero beyond the start set's own
    have hαb : ∀ k, |α k| ≤ 1 := by
      intro k
      by_cases hk : k < Rdelta.p
      · simp only [hα, dif_pos hk]
        exact ha₀ _
      · simp [hα, hk]
    have hαa : (fun k : Fin Rdelta.p => α k) = a₀ := funext fun k => by simp [hα]
    have hfib : x 0 - toRealVec xs ∈ Rdelta.fiber (fun k : Fin Rdelta.p => α k) := by
      rw [hαa]
      exact hfib0
    have htr : fm.HasTrackedStaticError xs U redFactor p Rdelta := htrack
    set vd := S.1.nominal.point (fun k : Fin S.1.p => α k) with hvd
    have hstat_fib : ∀ t ∈ Set.Icc 0 (toReal options.Δt),
        (fun i => Fin.append (x 0 - toRealVec xs) (u t - toRealVec U.c) ⬝ᵥ (Scalar.toRealMat
          ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ
            Fin.append (x 0 - toRealVec xs) (u t - toRealVec U.c)) / 2)
          ∈ S.1.fiber (fun k => α k) := fun t ht =>
      htr α hαb _ hfib _ (Zonotope.sub_center_mem_recenter (traj.input t ht))
    -- the input less the constant `vd` is in the input of `polyPointFloat`
    set Vt := (Vbase ⊞ E.1) ⊞ S.1.indepZonotope with hVt
    set Uset : Set (Vec ℝ n) := (fun z => z + vd) '' Vt.toSet with hUset
    have hUb : Bornology.IsBounded Uset :=
      ((Zonotope.isCompact_toSet Vt).image (continuous_id.add continuous_const)).isBounded
    have hUV : ∀ z ∈ Uset, z - vd ∈ Vt.toSet := by
      rintro _ ⟨y, hy, rfl⟩
      simpa using hy
    -- the field less `A (x - x✱)` is in the shifted input
    have hin : ∀ t ∈ Set.Icc 0 (toReal options.Δt), sys.f (x t) (u t)
        - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ Uset := by
      intro t ht
      refine ⟨_ - vd, ?_, sub_add_cancel _ _⟩
      have := Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) (Vbase ⊞ E.1) S.1.indepZonotope
        (Set.add_mem_add (hfield t ht)
          (PolyZonotope.sub_depPoint_mem_indepZonotope S.1 (hstat_fib t ht)))
      rwa [sub_add_sub_cancel] at this
    have lt3 := traj.linearize_sub (lsys := (LinearSys.canonicalFloat A : LinearSys 𝕋 n))
      (xs := toRealVec xs) (X₀ := Rdelta.toSet) (V := Uset)
      measurableSet_Icc (hRd _ traj.init) hin
    exact hback (LinearSys.IsCanonicalTrajectory.polyPointFloat_outer hΔt lt3 hαb hfib
      (PolyZonotope.depPoint_mem_fiber_depPart S.1 _) hUb hUV _ hRtp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
