module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.CanonicalFloatInput
public import CORALean.ContDynamics.LinearSys.Theorems.PolyOneStepClosedFormFloatTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.PolyOneStepClosedFormFloatTimePointOuter
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyLoopFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrAdaptiveFloatMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.FloatModelEnclosesBaseMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.FloatModelEnclosesMemOfFixedPoint
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeSub
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeFoldContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterZeroMem

@[expose] public section

/-!
# One step of CORA's `linReach` from a polynomial zonotope holds every run of the real system

`linReachLoopFloat_outer` with the start set a polynomial zonotope. The loop ends at an applied
error `e` whose box holds `VerrorDyn`, the remainder over `Rmax` (`abstrErrAdaptiveFloat_mem` at
order 2), `Rmax` being the zonotope of the window of the step with input
`V = f(z✱) ⊕ B(U - u✱) ⊕ [-e, e]`. So the field less `A (x - x✱)` lies in `V` on `Rmax`, and the
dominated runs are in the window (`aux_polyOneStepFloat_outer`), which `zonotope(·)` encloses. A
run of `sys` is in `Rmax` too by `Encloses.mem_of_fixedPoint`, which needs `f` Lipschitz in the
state near `Rmax`: `Encloses` gives it on the box of `Rmax` joined with `x✱` widened by `1`.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `order` – the order of equal exponent columns

## Hypotheses
* `h` – model encloses system

## Conclusion
* a successful step encloses every run over the step and at its end, before and after reduction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- The generator-free polynomial zonotope at `v` holds `v`. -/
private theorem aux_polyOneStep_mem_pt {k : ℕ} (v : Vec 𝕋 k) : -- --- CONCL ---
    toRealVec v ∈ (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 k)).ofIndep.toSet := by -- --- PROOF ---
  refine Zonotope.ofIndep_outer _ ?_
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩

/-- The inputs of the linearized system when `V` holds the field less its linear part: `V`,
through `B = I`, `c = 0`. -/
private abbrev aux_polyOneStep_W (A : Mat 𝕋 n n) (V : Zonotope (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  (fun u => Scalar.toRealMat (LinearSys.canonicalFloat A).B *ᵥ u +
    Scalar.toRealVec (LinearSys.canonicalFloat A).c) '' V.toSet

omit [ToRat 𝕋] in
/-- `δ = x - x✱` is a run of the linearized system from `R - x✱` over `[0, T]`, its input in the
image of `V` under `B = I`, `c = 0`. -/
private theorem aux_polyOneStep_linearize {sys : NonlinearSys n m} {A : Mat 𝕋 n n}
    {xs : Vec 𝕋 n} {V : Zonotope (Vec 𝕋 n)} {R : PolyZonotope (Vec 𝕋 n)} {T : ℝ}
    {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) (Set.Icc 0 T) R.toSet U x u y)
    (hV : ∀ t ∈ Set.Icc 0 T,
      sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ V.toSet) : -- --- CONCL ---
    (LinearSys.canonicalFloat A : LinearSys 𝕋 n).IsCanonicalTrajectory (S := ExactSet)
      (Set.Icc 0 T)
      (R ⊞ (⟨0, (-xs), fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope (Vec 𝕋 n)).ofIndep).toSet
      (aux_polyOneStep_W A V) (fun t => x t - toRealVec xs) fun t =>
      sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) := by -- --- PROOF ---
  refine traj.linearize_sub measurableSet_Icc ?_ fun t ht => ?_
  -- the start, `R - x✱`
  · have hneg : toRealVec (-xs) = -toRealVec xs := toRealVec_neg _
    have hp := aux_polyOneStep_mem_pt (-xs)
    rw [hneg] at hp
    have := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) R (⟨0, (-xs), fun j => j.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n)).ofIndep
      (Set.add_mem_add traj.init hp)
    rwa [← sub_eq_add_neg] at this
  -- the input, through `B = I`, `c = 0`
  · refine ⟨_, hV t ht, ?_⟩
    exact congrFun (LinearSys.canonicalFloat_input A) _

omit [ToRat 𝕋] in
/-- The inputs lie in `V` recentered around `V.c`, a bounded set. -/
private theorem aux_polyOneStep_recentered (A : Mat 𝕋 n n) (V : Zonotope (Vec 𝕋 n)) :
    (∀ v ∈ aux_polyOneStep_W A V, v - toRealVec V.c ∈ (Recenter.recenter V).toSet) ∧
      Bornology.IsBounded (aux_polyOneStep_W A V) := by
  have hid : aux_polyOneStep_W A V = V.toSet := by
    rw [aux_polyOneStep_W, LinearSys.canonicalFloat_input, Set.image_id]
  rw [hid]
  exact ⟨fun v hv => Zonotope.sub_center_mem_recenter hv, CompactSet.isBounded_toSet V⟩

omit [ToRat 𝕋] in
/-- Adding `x✱` back to a set holding `y - x✱` gives a set holding `y`. -/
private theorem aux_polyOneStep_back {xs : Vec 𝕋 n} {Z : PolyZonotope (Vec 𝕋 n)} {y : Vec ℝ n}
    (hy : y - toRealVec xs ∈ Z.toSet) :
    y ∈ toSet (Z ⊞ (⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 n)).ofIndep) := by
  have := Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) Z (⟨0, xs, fun j => j.elim0,
    ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n)).ofIndep
    (Set.add_mem_add hy (aux_polyOneStep_mem_pt xs))
  rwa [sub_add_cancel] at this

omit [ToRat 𝕋] in
/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
whose `f(x, u) - A(x - x✱)` stays in `V` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
private theorem aux_polyOneStepFloat_outer {sys : NonlinearSys n m} {A : Mat 𝕋 n n}
    {xs : Vec 𝕋 n} {V : Zonotope (Vec 𝕋 n)} {R : PolyZonotope (Vec 𝕋 n)}
    {options : LinearSys.ReachFloatOptions 𝕋}
    {order : ℕ → Array (Array ℕ) → Array ℕ} : -- --- CONCL ---
    ∀ M ∈ (LinearSys.canonicalFloat A : LinearSys 𝕋 n).closedFormMatricesFloat options.Δt
      (max 2 options.η), ∀ Rτ Rt,
      (Rτ, Rt) ∈ NonlinearSys.step_polyOneStepFloat A xs V R options order M →
      0 < toReal options.Δt ∧ ∀ {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
      {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt))
          R.toSet U x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt),
          sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ V.toSet) →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.toSet) ∧
          x (toReal options.Δt) ∈ Rt.toSet := by -- --- PROOF ---
  intro M hM Rτ Rt
    (hstep : NonlinearSys.step_polyOneStepFloat A xs V R options order M = some (Rτ, Rt))
  -- the positive width, and the closed-form step it ran
  unfold NonlinearSys.step_polyOneStepFloat at hstep
  dsimp only at hstep
  by_cases hpos : ltStrict (zero : 𝕋) options.Δt = true
  swap
  · simp [hpos] at hstep
  rw [if_pos hpos] at hstep
  have hΔt : 0 < toReal options.Δt := by
    simpa [toReal_zero] using toReal_lt_of_ltStrict hpos
  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  refine ⟨hΔt, fun {U x u y} traj hV => ?_⟩
  have ltraj := aux_polyOneStep_linearize traj hV
  -- the input is `V.c` and what `V` holds around it, which holds `0`
  obtain ⟨hWU, hW⟩ := aux_polyOneStep_recentered A V
  -- the closed-form step's theorems, at the window and at its end
  have hη : 2 ≤ max 2 options.η := le_max_left _ _
  refine ⟨fun t ht => ?_, ?_⟩
  · exact aux_polyOneStep_back (ltraj.polyOneStepClosedFormFloat_timeInterval_outer hη hΔt
      (Zonotope.zero_mem_recenter V) ht.1 ht.2 hWU hW M hM)
  · exact aux_polyOneStep_back (ltraj.polyOneStepClosedFormFloat_timePoint_outer hΔt hWU hW M hM)

omit [ToRat 𝕋] in
/-- `f(x, u) - A(x - x✱)` is in `f(z✱) ⊕ B(U - u✱) ⊕ L` once the remainder is in `L`. -/
private theorem aux_polyLoop_input {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) {U : Zonotope (Vec 𝕋 m)}
    {L : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n} {u : Vec ℝ m} (hu : u ∈ U.toSet)
    (hL : sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
      (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c)) ∈ L.toSet)
    : -- --- CONCL ---
    sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
      (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)) ⊞
          L).toSet := by -- --- PROOF ---
  have hsplit : sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      = (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c))
        + (sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
          (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c))) := by abel
  rw [hsplit]
  exact Plus.plus_outer _ L (Set.add_mem_add (h.base_mem B xs hu) hL)

omit [ToRat 𝕋] in
/-- A box within `e` in magnitude lies in the zonotope of `[-e, e]`. -/
private theorem aux_polyLoop_box {V : Zonotope (Vec 𝕋 n)} {e : Vec 𝕋 n}
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
/-- What the error loop returns: `Rmax` is the zonotope of the window of a step at some applied
error `e` whose box holds `VerrorDyn`, the remainder over `Rmax`. -/
private theorem aux_polyLoop_result {fm : NonlinearSys.FloatHessModel 𝕋 n m} [ToRat 𝕋]
    {A : Mat 𝕋 n n} {B : Mat 𝕋 n m} {xs : Vec 𝕋 n} {Vbase : Zonotope (Vec 𝕋 n)}
    {R : PolyZonotope (Vec 𝕋 n)}
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋}
    {maxError : Option (Vec 𝕋 n)} {order : ℕ → Array (Array ℕ) → Array ℕ}
    {M : LinearSys.ClosedFormMatrices 𝕋 n} : -- --- CONCL ---
    ∀ (fuel : ℕ) (err : Vec 𝕋 n) (res : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n),
      fm.step_abstrErrLoopLinPoly A B xs Vbase R U options enlarge maxError order M fuel err =
        some res →
      ∃ (e' : Vec 𝕋 n) (Rpz Rt : PolyZonotope (Vec 𝕋 n)), NonlinearSys.step_polyOneStepFloat A xs
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope) R options order M =
            some (Rpz, Rt) ∧ res.1 = Rpz.zonotopeFold.materialise ∧
        (∀ (redFactor : 𝕋) (p : ℕ),
          res.2.1 = fm.abstrErrAdaptiveFloat 2 A B xs res.1 U redFactor p) ∧
        ∀ i, le (res.2.1.interval.normMag i) (e' i) = true := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro err res hres; simp [NonlinearSys.FloatHessModel.step_abstrErrLoopLinPoly] at hres
  | succ fuel ih =>
    intro err res hres
    unfold NonlinearSys.FloatHessModel.step_abstrErrLoopLinPoly at hres
    dsimp only at hres
    split at hres
    · exact absurd hres (by simp)
    · rename_i Rpz Rt' hstep
      split_ifs at hres with hmax hconv
      · simp only [Option.some.injEq] at hres
        subst hres
        exact ⟨_, Rpz, Rt', hstep, rfl, fun _ _ => rfl, hconv⟩
      · exact ih _ _ hres


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R` under
inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachPolyLoopFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {R : PolyZonotope (Vec 𝕋 n)} {abstrerr : Vec 𝕋 n} {maxError : Option (Vec 𝕋 n)}
    {order : ℕ → Array (Array ℕ) → Array ℕ} : -- --- CONCL ---
    ∀ Rτ Rt err, (Rτ, Rt, err) ∈ fm.linReachPolyLoopFloat U options enlarge fuel R abstrerr
        maxError order →
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U.toSet x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.toSet) ∧
          x (toReal options.Δt) ∈ Rt.toSet := by -- --- PROOF ---
  intro Rτ Rt err (hP : fm.linReachPolyLoopFloat U options enlarge fuel R abstrerr maxError order
    = some (Rτ, Rt, err))
  unfold NonlinearSys.FloatHessModel.linReachPolyLoopFloat at hP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hP
  obtain ⟨M, hM, E, hE, S, hS, hpure⟩ := hP
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl, -⟩ := hpure
  set xs := (fm.linPointFloat options.Δt ⟨0, R.c, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
    U).1
  set A := (fm.linearizeFloat xs U.c).1
  set B := (fm.linearizeFloat xs U.c).2
  set Vbase := (fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  -- the loop's last pass: `Rmax` at some applied error whose box holds `VerrorDyn`
  obtain ⟨e', Rpz, Rt', hmax, hRmax, hV, hle⟩ := aux_polyLoop_result _ _ E hE
  -- on `Rmax`, the field less `A (x - x✱)` is in the final input, and in the loop's
  have hrem : ∀ {x : Vec ℝ n} {v : Vec ℝ m}, x ∈ E.1.toSet → v ∈ U.toSet →
      sys.f x v - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
        (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (v - toRealVec U.c)) ∈ E.2.1.toSet :=
    fun hx hv => (hV one 0) ▸ h.abstrErrAdaptiveFloat_mem 2 A B xs E.1 U one 0 hx hv
  have hlin : ∀ {x : Vec ℝ n} {v : Vec ℝ m}, x ∈ E.1.toSet → v ∈ U.toSet →
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈ (Vbase ⊞ E.2.1).toSet :=
    fun hx hv => aux_polyLoop_input h.toEncloses A B xs hv (hrem hx hv)
  have hlin' : ∀ x ∈ E.1.toSet, ∀ v ∈ U.toSet,
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
        (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet :=
    fun x hx v hv => aux_polyLoop_input h.toEncloses A B xs hv
      (aux_polyLoop_box hle (hrem hx hv))
  -- the dominated runs are in `Rmax`
  obtain ⟨hΔt, _⟩ := aux_polyOneStepFloat_outer (sys := sys) M hM _ _ hmax
  -- every run dominated by the loop's input is in `Rmax`
  have hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
      (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
      sys'.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U' x' u' y' →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), sys'.f (x' t) (u' t)
        - Scalar.toRealMat A *ᵥ (x' t - toRealVec xs) ∈
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet) →
      ∀ t ∈ Set.Icc 0 (toReal options.Δt), x' t ∈ E.1.toSet :=
    fun m' sys' U' x' u' y' traj' hin t ht => by
      rw [hRmax, Zonotope.materialise_eq]
      exact PolyZonotope.zonotopeFold_contains Rpz
        (((aux_polyOneStepFloat_outer (sys := sys') M hM _ _ hmax).2 traj' hin).1 t ht)
  -- the final step holds every run whose field is in its input
  obtain ⟨-, hout⟩ := aux_polyOneStepFloat_outer (sys := sys) M hM _ _ hS
  refine ⟨hΔt, fun {x u y} traj => ?_⟩
  -- the loop's input set is bounded and holds a point, the base point and the box's origin
  have hVb : Bornology.IsBounded (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet :=
    (Zonotope.isCompact_toSet _).isBounded
  have hVne : (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet.Nonempty := by
    have h0 : (0 : Vec ℝ n) ∈ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).toSet := fun i => by
      have h1 := toReal_le_of_le (hle i)
      have h2 : 0 ≤ toReal (E.2.1.interval.normMag i) := by
        rw [Interval.normMag, toReal_maximum, toReal_absolute]
        exact le_max_of_le_left (abs_nonneg _)
      show toReal ((-e') i) ≤ 0 ∧ 0 ≤ toReal (e' i)
      rw [show (-e') i = neg (e' i) from rfl, toReal_neg]
      constructor <;> linarith
    exact ⟨_, Plus.plus_outer Vbase _ (Set.add_mem_add
      (h.toEncloses.base_mem B xs (traj.input 0 ⟨le_rfl, hΔt.le⟩))
      (Interval.zonotope_contains _ h0))⟩
  -- the run stays in `Rmax`
  have hconf := h.toEncloses.mem_of_fixedPoint (sys := sys) hΔt.le (K := E.1.toSet) E.1
    (Scalar.toRealMat A) xs hVb hVne (Zonotope.isCompact_toSet E.1).isClosed subset_rfl
    hdom hlin' traj
  exact hout traj fun t ht => hlin (hconf t ht) (traj.input t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
