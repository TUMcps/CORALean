import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryPostDeltaFloatOuter
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolyFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.HessRemainderAbstractionError
import CORALean.ContDynamics.NonlinearSys.Theorems.OneStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RegionFloatConfined
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem

/-!
# One float `linReach` step holds every run of the real system

A run of `ẋ = f(x, u)` on `[0, Δt]` from `R` under inputs in `U` stays in the checked
region (`regionFloat_confined`), so at every time `f(x, u) - A(x - x✱)` is
`f(z✱) + B(u - u✱)` plus the remainder, which lies in `L`, and `oneStepFloat_outer`
does the rest. At `'lin'`, `L` is `hessRemainder`, an abstraction-error certificate.
At `'poly'` it is `abstrErrPolyFloat`, which needs the run's differences from its start:
the `'lin'` membership makes `x - x✱` a run of the linearized system with inputs in
`Vlin`, so `postDeltaFloat_outer` places `x(t) - x(0)` in `Rdiff`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- The generator-free zonotope at `v` holds `v`. -/
theorem aux_linReach_mem_pt {k : ℕ} (v : Vec 𝕋 k) :
    toRealVec v ∈ (⟨0, v, fun _ j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope 𝕋 k).construct := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩

omit [ToRat 𝕋] in
/-- A box widened to a point holds the box and the point. -/
theorem aux_linReach_mem_hull {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec 𝕋 k) :
    I.construct ⊆ (⟨fun i => minimum (I.inf i) (v i), fun i => maximum (I.sup i) (v i)⟩ :
      Interval (Vec 𝕋 k)).construct ∧ toRealVec v ∈ (⟨fun i => minimum (I.inf i) (v i),
        fun i => maximum (I.sup i) (v i)⟩ : Interval (Vec 𝕋 k)).construct := by -- --- PROOF ---
  refine ⟨fun y hy i => ?_, fun i => ?_⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ y i ∧ y i ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_of_left_le (hy i).1, le_max_of_le_left (hy i).2⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ toReal (v i)
      ∧ toReal (v i) ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

omit [ToRat 𝕋] in
/-- `f(x, u) - A(x - x✱)` is in `f(z✱) ⊕ B(U - u✱) ⊕ L` once the remainder is in `L`. -/
theorem aux_linReach_input {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) {U : Zonotope 𝕋 m}
    {L : Zonotope 𝕋 n} {x : Vec ℝ n} {u : Vec ℝ m} (hu : u ∈ U.construct)
    (hL : sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ
      (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c)) ∈ L.construct) :
    sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
      (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) B (Recentre.recentre U)) ⊞ L).construct := by -- --- PROOF ---
  set us := toRealVec U.c
  have hf₀ : sys.f (toRealVec xs) us ∈ (fm.f (Interval.point xs) (Interval.point U.c)).construct :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  have hBu : Scalar.toRealMat B *ᵥ (u - us) ∈ construct (Mtimes.mtimes (𝕄 := Mat 𝕋) B
      (Recentre.recentre U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) B _ (Set.mem_biUnion (Set.mem_singleton _)
      (Set.mem_image_of_mem _ (Zonotope.sub_centre_mem_recentre hu)))
  have hsplit : sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      = (sys.f (toRealVec xs) us + Scalar.toRealMat B *ᵥ (u - us))
        + (sys.f x u - (sys.f (toRealVec xs) us + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
          + Scalar.toRealMat B *ᵥ (u - us))) := by abel
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Interval.zonotope_contains _ hf₀) hBu)) hL)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
under inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.linReachFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {alg : NonlinearSys.LinReachAlg} {U : Zonotope 𝕋 m} {options : LinearSys.ReachOptions 𝕋}
    {R Rτ Rt : Zonotope 𝕋 n} (hstep : fm.linReachFloat alg U options R = some (Rτ, Rt)) :
    0 < toReal options.timeStep ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal options.timeStep))
        R.construct U.construct x u →
      (∀ t ∈ Set.Icc 0 (toReal options.timeStep), x t ∈ Rτ.construct) ∧
        x (toReal options.timeStep) ∈ Rt.construct := by -- --- PROOF ---
  unfold NonlinearSys.FloatHessModel.linReachFloat at hstep
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨Ω, hΩ, hrest⟩ := hstep
  set Δt := options.timeStep with hΔt_def
  set xs := (fm.linPointFloat Δt R U).1 with hxs_def
  set A := (fm.linearizeFloat xs U.c).1 with hA_def
  set B := (fm.linearizeFloat xs U.c).2 with hB_def
  set X : Interval (Vec 𝕋 n) :=
    ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩ with hX_def
  set U' : Interval (Vec 𝕋 m) :=
    ⟨fun i => minimum (U.interval.inf i) (U.c i), fun i => maximum (U.interval.sup i) (U.c i)⟩
  have hUU' : U.construct ⊆ U'.construct :=
    fun v hv => (aux_linReach_mem_hull U.interval U.c).1 (Zonotope.interval_contains U hv)
  have hxsX := (aux_linReach_mem_hull Ω xs).2
  have husU' := (aux_linReach_mem_hull U.interval U.c).2
  -- a run stays in `Ω`, so in `X`
  have hconf : 0 < toReal Δt → ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal Δt)) R.construct
        U.construct x u → ∀ t ∈ Set.Icc 0 (toReal Δt), x t ∈ X.construct :=
    fun hΔt {x u} traj t ht => (aux_linReach_mem_hull Ω xs).1
      (h.regionFloat_confined hΩ hΔt.le traj (Zonotope.interval_contains U) (a := 0)
        (by rw [zero_add]) (Zonotope.interval_contains R traj.init) t (by rwa [zero_add]))
  -- the `'lin'` input set holds the field less its linear part
  have hlin : ∀ {x : Vec ℝ n} {u : Vec ℝ m}, x ∈ X.construct → u ∈ U.construct →
      sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs) ∈
        (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
          Mtimes.mtimes (𝕄 := Mat 𝕋) B (Recentre.recentre U)) ⊞
            (fm.hessRemainder A B xs U.c X U').zonotope).construct := fun {x u} hx hu =>
    aux_linReach_input h.toEncloses A B xs hu (Interval.zonotope_contains _
      ((h.hessRemainder_abstractionError A B hxsX husU').encloses x hx u (hUU' hu)))
  cases alg with
  | lin =>
    obtain ⟨hΔt, hout⟩ := NonlinearSys.oneStepFloat_outer hrest
    exact ⟨hΔt, fun traj => hout traj fun t ht => hlin (hconf hΔt traj t ht) (traj.input t ht)⟩
  | poly errorOrder =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrest
    obtain ⟨η, hη, hone⟩ := hrest
    obtain ⟨hΔt, hout⟩ := NonlinearSys.oneStepFloat_outer hone
    refine ⟨hΔt, fun {x u} traj => hout traj fun t ht => ?_⟩
    set Rdelta := R ⊞ (⟨0, fun i => neg (xs i), fun _ j => j.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope 𝕋 n) with hRdelta
    -- the start, `x(0) - x✱ ∈ Rdelta`
    have hx₀ : x 0 - toRealVec xs ∈ Rdelta.construct := by
      have hneg : toRealVec (fun i => neg (xs i)) = -toRealVec xs := by
        funext i; exact toReal_neg (xs i)
      have hp := aux_linReach_mem_pt (fun i => neg (xs i))
      rw [hneg] at hp
      have := Plus.plus_outer R (⟨0, fun i => neg (xs i), fun _ j => j.elim0,
        ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope 𝕋 n) (Set.add_mem_add traj.init hp)
      rwa [← sub_eq_add_neg] at this
    -- `x - x✱` is a run of the `'lin'` linearization, so its differences are in `Rdiff`
    have ltraj : (⟨A⟩ : LinearSys 𝕋 n).Trajectory (S := fun k => Set (Vec ℝ k))
        (Set.Icc 0 (toReal Δt)) Rdelta.construct
        (((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
          Mtimes.mtimes (𝕄 := Mat 𝕋) B (Recentre.recentre U)) ⊞
            (fm.hessRemainder A B xs U.c X U').zonotope).construct
        (fun t => x t - toRealVec xs)
        (fun t => sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs)) :=
      ⟨hx₀, fun s hs => hlin (hconf hΔt traj s hs) (traj.input s hs), fun s hs => by
        refine ((traj.flow s hs).sub_const (toRealVec xs)).congr_deriv ?_
        show sys.f (x s) (u s) = Scalar.toRealMat A *ᵥ (x s - toRealVec xs)
          + (sys.f (x s) (u s) - Scalar.toRealMat A *ᵥ (x s - toRealVec xs))
        abel⟩
    have hδ := ltraj.postDeltaFloat_outer hΔt (LinearSys.reachOrderFloat_spec hη).1
      subset_rfl ht
    simp only [sub_sub_sub_cancel_right] at hδ
    -- the remainder at `x(t)`, inside `abstrErrPolyFloat`
    exact aux_linReach_input h.toEncloses A B xs (traj.input t ht)
      (h.abstrErrPolyFloat_outer A B hxsX husU' (hconf hΔt traj t ht) (hUU' (traj.input t ht))
        (Reduce.reduce_outer Rdelta errorOrder hx₀) hδ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
