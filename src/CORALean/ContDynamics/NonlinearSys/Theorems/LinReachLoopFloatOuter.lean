module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachLoopFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrAdaptiveFloatMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryMemOfFixedPoint
public import CORALean.ContDynamics.NonlinearSys.Theorems.OneStepFloatOuter
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem

@[expose] public section

/-!
# One step of CORA's `linReach` with its error loop holds every run of the real system

The loop ends at an applied error `e` whose box holds `VerrorDyn`, the remainder over `Rmax`
(`abstrErrAdaptiveFloat_mem` at order 2), `Rmax` being the window of the linear step with input
`V = f(z✱) ⊕ B(U - u✱) ⊕ [-e, e]`. So the field less `A (x - x✱)` lies in `V` on `Rmax`, and the
dominated runs are in `Rmax` (`oneStepFloat_outer`). A run of `sys` is in `Rmax` too by
`IsTrajectory.mem_of_fixedPoint`, which needs `f` Lipschitz in the state near `Rmax`: `Encloses`
gives it on the box of `Rmax` joined with `x✱` widened by `1`. Then `oneStepFloat_outer`
finishes. No region is checked, and nothing beyond `Encloses` is assumed.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error
* `fuel` – iteration bound
* `R` – start zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `step` – linear step

## Hypotheses
* `h` – model encloses system

## Conclusion
* a successful step encloses every run over the step and at its end
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- `f(x✱, u✱) + B (u - u✱)` is in `f(z✱) ⊕ B(U - u✱)`. -/
private theorem aux_loop_base {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) {U : Zonotope (Vec 𝕋 m)}
    {u : Vec ℝ m} (hu : u ∈ U.toSet) : -- --- CONCL ---
    sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c) ∈
      ((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
          (Recenter.recenter U)).toSet := by -- --- PROOF ---
  -- the base point is the field at the expansion point; the input part is the recentered `U`
  have hf₀ : sys.f (toRealVec xs) (toRealVec U.c) ∈
      (fm.f (Interval.point xs) (Interval.point U.c)).toSet :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  have hBu : Scalar.toRealMat B *ᵥ (u - toRealVec U.c) ∈ toSet
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
      (Recenter.recenter U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion (Set.mem_singleton _)
      (Set.mem_image_of_mem _ (Zonotope.sub_center_mem_recenter hu)))
  exact Plus.plus_outer _ _ (Set.add_mem_add (Interval.zonotope_contains _ hf₀) hBu)

omit [ToRat 𝕋] in
/-- `f(x, u) - A(x - x✱)` is in `f(z✱) ⊕ B(U - u✱) ⊕ L` once the remainder is in `L`. -/
private theorem aux_loop_input {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
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
  exact Plus.plus_outer _ L (Set.add_mem_add (aux_loop_base h B xs hu) hL)

omit [ToRat 𝕋] in
/-- A box within `e` in magnitude lies in the zonotope of `[-e, e]`. -/
private theorem aux_loop_box {V : Zonotope (Vec 𝕋 n)} {e : Vec 𝕋 n}
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
/-- The slope matrices of a box bound the field's change in the state, over the box. -/
private theorem aux_loop_lipschitz {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (X : Interval (Vec 𝕋 n))
    (Ub : Interval (Vec 𝕋 m)) : -- --- CONCL ---
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ X.toSet, ∀ y' ∈ X.toSet, ∀ v ∈ Ub.toSet,
      ‖sys.f y v - sys.f y' v‖ ≤ L * ‖y - y'‖ := by -- --- PROOF ---
  set M := fm.jacX X Ub with hM
  set S : ℝ := ∑ i, ∑ k, (|toReal (M.inf i k)| + |toReal (M.sup i k)|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  refine ⟨n * S, by positivity, fun y hy y' hy' v hv => ?_⟩
  obtain ⟨Jx, hJx, Ju, -, hslope⟩ := h.slope_mem X Ub y hy y' hy' v hv v hv
  rw [hslope, sub_self, Matrix.mulVec_zero, add_zero]
  -- every entry of `Jx` is at most `S`
  have hent : ∀ i k, |Jx i k| ≤ S := by
    intro i k
    obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hJx i k
    have hle : |Jx i k| ≤ |toReal (M.inf i k)| + |toReal (M.sup i k)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (toReal (M.inf i k)), abs_nonneg (toReal (M.sup i k))]
      · linarith [le_abs_self (toReal (M.sup i k)), abs_nonneg (toReal (M.inf i k))]
    -- and a single term is at most the double sum
    refine hle.trans ?_
    calc |toReal (M.inf i k)| + |toReal (M.sup i k)|
        ≤ ∑ k', (|toReal (M.inf i k')| + |toReal (M.sup i k')|) :=
          Finset.single_le_sum (f := fun k' => |toReal (M.inf i k')| + |toReal (M.sup i k')|)
            (fun k' _ => by positivity) (Finset.mem_univ k)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ k', (|toReal (M.inf i' k')| +
            |toReal (M.sup i' k')|)) (fun i' _ => Finset.sum_nonneg fun k' _ => by positivity)
            (Finset.mem_univ i)
  -- each row of `Jx (y - y')` is at most `n S ‖y - y'‖`
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(Jx *ᵥ (y - y')) i| = |∑ k, Jx i k * (y - y') k| := rfl
    _ ≤ ∑ k, |Jx i k * (y - y') k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, S * ‖y - y'‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hent i k) (by simpa using norm_le_pi_norm (y - y') k) (abs_nonneg _) hS0
    _ = n * S * ‖y - y'‖ := by simp [mul_assoc]

omit [ToRat 𝕋] in
/-- A point of a box is in the interior of the box widened by `1` on every side. -/
private theorem aux_loop_ball {X : Interval (Vec 𝕋 n)} {y : Vec ℝ n}
    (hy : y ∈ X.toSet) : -- --- CONCL ---
    Metric.ball y 1 ⊆ (⟨fun i => subDown (X.inf i) one, fun i => addUp (X.sup i) one⟩ :
      Interval (Vec 𝕋 n)).toSet := by -- --- PROOF ---
  intro z hz i
  have hd : |z i - y i| < 1 := by
    have := dist_le_pi_dist z y i
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this (Metric.mem_ball.mp hz)
  obtain ⟨hd1, hd2⟩ := abs_lt.mp hd
  have r1 := subDown_le_sub (X.inf i) one
  have r2 := add_le_addUp (X.sup i) one
  rw [toReal_one] at r1 r2
  have hy1 : toReal (X.inf i) ≤ y i := (hy i).1
  have hy2 : y i ≤ toReal (X.sup i) := (hy i).2
  exact ⟨by show toReal (subDown (X.inf i) one) ≤ z i; linarith,
    by show z i ≤ toReal (addUp (X.sup i) one); linarith⟩

omit [ToRat 𝕋] in
/-- What the error loop returns: `Rmax` is the window of a linear step at some applied error `e`
whose box holds `VerrorDyn`, the remainder over `Rmax`. -/
private theorem aux_loop_result {fm : NonlinearSys.FloatHessModel 𝕋 n m} [ToRat 𝕋]
    {A : Mat 𝕋 n n} {B : Mat 𝕋 n m} {xs : Vec 𝕋 n} {Vbase R : Zonotope (Vec 𝕋 n)}
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋}
    {maxError : Option (Vec 𝕋 n)} {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ (fuel : ℕ) (err : Vec 𝕋 n) (res : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n),
      fm.step_abstrErrLoopLin A B xs Vbase R U options enlarge maxError step fuel err = some res →
      ∃ (e' : Vec 𝕋 n) (Rt : Zonotope (Vec 𝕋 n)), NonlinearSys.oneStepFloat A xs
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope) R options step =
            some (res.1, Rt) ∧
        (∀ (redFactor : 𝕋) (p : ℕ),
          res.2.1 = fm.abstrErrAdaptiveFloat 2 A B xs res.1 U redFactor p) ∧
        ∀ i, le (res.2.1.interval.normMag i) (e' i) = true := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro err res hres; simp [NonlinearSys.FloatHessModel.step_abstrErrLoopLin] at hres
  | succ fuel ih =>
    intro err res hres
    unfold NonlinearSys.FloatHessModel.step_abstrErrLoopLin at hres
    dsimp only at hres
    split at hres
    · exact absurd hres (by simp)
    · rename_i Rmax Rt' hstep
      split_ifs at hres with hmax hconv
      · simp only [Option.some.injEq] at hres
        subst hres
        exact ⟨_, Rt', hstep, fun _ _ => rfl, hconv⟩
      · exact ih _ _ hres


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R` under
inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachLoopFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {R : Zonotope (Vec 𝕋 n)} {abstrerr : Vec 𝕋 n} {maxError : Option (Vec 𝕋 n)}
    {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ Rτ Rt err, (Rτ, Rt, err) ∈ fm.linReachLoopFloat U options enlarge fuel R abstrerr maxError
        step →
      0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U.toSet x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.toSet) ∧
          x (toReal options.Δt) ∈ Rt.toSet := by -- --- PROOF ---
  intro Rτ Rt err (hP : fm.linReachLoopFloat U options enlarge fuel R abstrerr maxError step
    = some (Rτ, Rt, err))
  unfold NonlinearSys.FloatHessModel.linReachLoopFloat at hP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hP
  obtain ⟨E, hE, S, hS, hpure⟩ := hP
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl, -⟩ := hpure
  set xs := (fm.linPointFloat options.Δt R U).1
  set A := (fm.linearizeFloat xs U.c).1
  set B := (fm.linearizeFloat xs U.c).2
  set Vbase := (fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  -- the loop's last pass: `Rmax` at some applied error whose box holds `VerrorDyn`
  obtain ⟨e', Rt', hmax, hV, hle⟩ := aux_loop_result _ _ E hE
  -- on `Rmax`, the field less `A (x - x✱)` is in the final input, and in the loop's
  have hrem : ∀ {x : Vec ℝ n} {v : Vec ℝ m}, x ∈ E.1.toSet → v ∈ U.toSet →
      sys.f x v - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
        (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (v - toRealVec U.c)) ∈ E.2.1.toSet :=
    fun hx hv => (hV one 0) ▸ h.abstrErrAdaptiveFloat_mem 2 A B xs E.1 U one 0 hx hv
  have hlin : ∀ {x : Vec ℝ n} {v : Vec ℝ m}, x ∈ E.1.toSet → v ∈ U.toSet →
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈ (Vbase ⊞ E.2.1).toSet :=
    fun hx hv => aux_loop_input h.toEncloses A B xs hv (hrem hx hv)
  have hlin' : ∀ x ∈ E.1.toSet, ∀ v ∈ U.toSet,
      sys.f x v - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
        (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet :=
    fun x hx v hv => aux_loop_input h.toEncloses A B xs hv (aux_loop_box hle (hrem hx hv))
  -- the dominated runs are in `Rmax`
  obtain ⟨hΔt, _⟩ := NonlinearSys.oneStepFloat_outer (sys := sys) _ _ hmax
  -- every run dominated by the loop's input is in `Rmax`
  have hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
      (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
      sys'.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt)) R.toSet U' x' u' y' →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), sys'.f (x' t) (u' t)
        - Scalar.toRealMat A *ᵥ (x' t - toRealVec xs) ∈
          (Vbase ⊞ (⟨-e', e'⟩ : Interval (Vec 𝕋 n)).zonotope).toSet) →
      ∀ t ∈ Set.Icc 0 (toReal options.Δt), x' t ∈ E.1.toSet :=
    fun m' sys' U' x' u' y' traj' hin =>
      ((NonlinearSys.oneStepFloat_outer (sys := sys') _ _ hmax).2 traj' hin).1
  -- the final step holds every run whose field is in its input
  obtain ⟨-, hout⟩ := NonlinearSys.oneStepFloat_outer (sys := sys) _ _ hS
  refine ⟨hΔt, fun {x u y} traj => ?_⟩
  -- the box `Rmax` joined with `x✱`, widened by `1`, is where the field is Lipschitz
  set X : Interval (Vec 𝕋 n) := ⟨fun i => minimum (E.1.interval.inf i) (xs i),
    fun i => maximum (E.1.interval.sup i) (xs i)⟩ with hX
  have hKX : E.1.toSet ⊆ X.toSet := fun y hy i => by
    obtain ⟨h1, h2⟩ := Zonotope.interval_contains E.1 hy i
    show toReal (minimum (E.1.interval.inf i) (xs i)) ≤ y i ∧
      y i ≤ toReal (maximum (E.1.interval.sup i) (xs i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_of_left_le h1, le_max_of_le_left h2⟩
  obtain ⟨L, hL0, hL⟩ := aux_loop_lipschitz h.toEncloses
    (⟨fun i => subDown (X.inf i) one, fun i => addUp (X.sup i) one⟩ : Interval (Vec 𝕋 n))
    U.interval
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
      (aux_loop_base h.toEncloses B xs (traj.input 0 ⟨le_rfl, hΔt.le⟩))
      (Interval.zonotope_contains _ h0))⟩
  -- the run stays in `Rmax`
  have hconf := NonlinearSys.IsTrajectory.mem_of_fixedPoint (sys := sys) hΔt.le
    (K := E.1.toSet) (Scalar.toRealMat A) (toRealVec xs) hVb hVne
    (Zonotope.isCompact_toSet E.1).isClosed (fun y hy => aux_loop_ball (hKX hy)) hL0
    (fun y hy y' hy' v hv => hL y hy y' hy' v (Zonotope.interval_contains U hv))
    hdom hlin' traj
  exact hout traj fun t ht => hlin (hconf t ht) (traj.input t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
