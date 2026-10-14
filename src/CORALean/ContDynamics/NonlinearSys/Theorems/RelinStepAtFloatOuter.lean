module

public import CORALean.ContDynamics.LinearSys.Theorems.CanonicalFloatInput
public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputTimePointOuter
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepAtFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.RegionFloatConfined
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

@[expose] public section

/-!
# One float re-linearization step, at a given point, holds every run of the real system

A run of `ẋ = f(x, u)` on `[0, Δt]` from `R` under inputs in `U` stays in the
checked region (`regionFloat_confined`), so `δ = x - x✱` is a run of the
linearized system `δ̇ = A δ + ũ` with `ũ = f(x, u) - A δ` in `linInputFloat`
(`linInputFloat_outer`), from `R - x✱`. `reachFloatInput_outer` and its
time-point twin place `δ` over the window and at its end, and adding `x✱` back
places `x`. No certificate and no confinement is asked of the caller.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- The generator-free zonotope at `v` holds `v`. -/
theorem aux_mem_pt {k : ℕ} (v : Vec 𝕋 k) :
    toRealVec v ∈ (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 k)).construct := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩

omit [ToRat 𝕋] in
/-- A box widened to a point holds the box and the point. -/
theorem aux_mem_hull {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec 𝕋 k) :
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step, at any expansion point, has a positive width, and every run of `sys` on
`[0, Δt]` from `R` under inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatModel.Encloses.relinStepAtFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {R Rτ Rt : Zonotope (Vec 𝕋 n)}
    {xs : Vec 𝕋 n} (hstep : fm.relinStepAtFloat U options R xs = some (Rτ, Rt)) :
    0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := 𝒮) (Set.Icc 0 (toReal options.Δt))
        R.construct U.construct x u →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.construct) ∧
        x (toReal options.Δt) ∈ Rt.construct := by -- --- PROOF ---
  -- every `←` of the step succeeded: name what each returned
  unfold NonlinearSys.FloatModel.relinStepAtFloat at hstep
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨Ω, hΩ, ⟨Rti, Rtp⟩, hS, Δτ, hτ, Δ₁, h₁, hpure⟩ := hstep
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  set Δt := options.Δt with hΔt_def
  set A := (fm.linearizeFloat xs U.c).1 with hA_def
  set B := (fm.linearizeFloat xs U.c).2 with hB_def
  set X : Interval (Vec 𝕋 n) :=
    ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩ with hX_def
  set U' : Interval (Vec 𝕋 m) :=
    ⟨fun i => minimum (U.interval.inf i) (U.c i), fun i => maximum (U.interval.sup i) (U.c i)⟩
  obtain ⟨hΔt, -⟩ := LinearSys.reachFloatInput_invariant _ hS
  refine ⟨hΔt, fun {x u} traj => ?_⟩
  -- the horizon `reachFloatInput` was given is the step
  have hTf : (((ToRat.toRat Δt : ℚ) : ℝ) - ((0 : ℚ) : ℝ)) = toReal Δt := by
    rw [ToRat.toReal_toRat, Rat.cast_zero, sub_zero]
  -- the run stays in `Ω`, so in `X`, and its inputs in `U'`
  have hconf := h.regionFloat_confined hΩ hΔt.le traj
    (Zonotope.interval_contains U) (a := 0) (by rw [zero_add])
    (Zonotope.interval_contains R traj.init)
  have hxX : ∀ t ∈ Set.Icc 0 (toReal Δt), x t ∈ X.construct := fun t ht =>
    (aux_mem_hull Ω xs).1 (hconf t (by rwa [zero_add]))
  have hUU' : U.construct ⊆ U'.construct :=
    fun v hv => (aux_mem_hull U.interval U.c).1 (Zonotope.interval_contains U hv)
  -- `δ = x - x✱` is a run of the linearized system from `R - x✱`
  have ltrajC : (LinearSys.canonicalFloat A : LinearSys 𝕋 n).CanonicalClassicalTrajectory (S := 𝒮)
      (Set.Icc 0 (((ToRat.toRat Δt : ℚ) : ℝ) - ((0 : ℚ) : ℝ)))
      (R ⊞ (⟨0, fun i => neg (xs i), fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope (Vec 𝕋 n))).construct
      ((fun u => Scalar.toRealMat (LinearSys.canonicalFloat A).B *ᵥ u +
        Scalar.toRealVec (LinearSys.canonicalFloat A).c) ''
        (fm.linInputFloat A B xs X U U').construct)
      (fun t => x t - toRealVec xs)
      (fun t => sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs)) := by
    refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
    -- the start, `R - x✱`
    · have hneg : toRealVec (fun i => neg (xs i)) = -toRealVec xs := by
        funext i; exact toReal_neg (xs i)
      have hp := aux_mem_pt (fun i => neg (xs i))
      rw [hneg] at hp
      have := Plus.plus_outer R (⟨0, fun i => neg (xs i), fun j => j.elim0,
        ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n)) (Set.add_mem_add traj.init hp)
      rwa [← sub_eq_add_neg] at this
    -- the input, through `B = I`, `c = 0`
    · rw [hTf] at ht
      refine ⟨_, h.linInputFloat_outer A B (aux_mem_hull Ω xs).2 hUU'
        (aux_mem_hull U.interval U.c).2 (hxX t ht) (traj.input t ht), ?_⟩
      exact congrFun (LinearSys.canonicalFloat_input A) _
    -- the flow, `δ̇ = ẋ = A δ + (f - A δ)`
    · have ht' : t ∈ Set.Icc 0 (toReal Δt) := by rwa [hTf] at ht
      have hd := (traj.flow t ht').sub_const (toRealVec xs)
      rw [hTf]
      refine hd.congr_deriv ?_
      show sys.f (x t) (u t) = Scalar.toRealMat A *ᵥ (x t - toRealVec xs)
        + (sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs))
      abel
  -- a classical run on `[0, Δt]` with its input in a compact set is a Carathéodory one
  have hVb : Bornology.IsBounded
      ((fun u => Scalar.toRealMat (LinearSys.canonicalFloat A).B *ᵥ u +
        Scalar.toRealVec (LinearSys.canonicalFloat A).c) ''
        (fm.linInputFloat A B xs X U U').construct) := by
    rw [LinearSys.canonicalFloat_input, Set.image_id]
    exact (Zonotope.isCompact_construct _).isBounded
  have ltraj := ltrajC.trajectory (convex_Icc _ _) ⟨le_rfl, by rw [hTf]; exact hΔt.le⟩ hVb
  obtain ⟨N, -, hlen, hout⟩ := LinearSys.reachFloatInput_outer _ hS
  obtain ⟨N', -, -, hout'⟩ := LinearSys.reachFloatInput_timePoint_outer _ hS
  -- adding `x✱` back
  have hback : ∀ {Z : Zonotope (Vec 𝕋 n)} {y : Vec ℝ n}, y - toRealVec xs ∈ Z.construct →
      y ∈ construct (Z ⊞ (⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope (Vec 𝕋 n))) := fun {Z y} hy => by
    have := Plus.plus_outer Z (⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 n)) (Set.add_mem_add hy (aux_mem_pt xs))
    rwa [sub_add_cancel] at this
  refine ⟨fun t ht => ?_, ?_⟩
  · cases Rti with
    | nil => simp at hτ
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hτ
      subst hτ
      refine hback (hout ltraj 0 (by simp) t ⟨by simpa using ht.1, by simpa using ht.2⟩)
  · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h₁
    have := hout' ltraj 1 hk
    rw [Nat.cast_one, one_mul] at this
    exact hback this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
