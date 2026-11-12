module

public import CORALean.ContDynamics.LinearSys.Theorems.CanonicalFloatInput
public import CORALean.ContDynamics.LinearSys.Theorems.IsReachFloatInputInvariant
public import CORALean.ContDynamics.LinearSys.Theorems.OneStepClosedFormFloatTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.OneStepClosedFormFloatTimePointOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputTimePointOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeSub
public import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterZeroMem
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

@[expose] public section

/-!
# One linearized step holds every run whose field it covers

A run of `ẋ = f(x, u)` on `[0, Δt]` from `R` whose `f(x, u) - A(x - x✱)` stays in `V` is,
in `δ = x - x✱`, a run of `δ̇ = A δ + ũ` from `R - x✱` with `ũ ∈ V`.
`reachFloatInput_outer` and its time-point twin place `δ` over the window and at its
end, and adding `x✱` back places `x`. The argument of `relinStepFloat_outer` with
the input set left to the caller.

## Inputs
* `sys` – system
* `A` – state matrix
* `xs` – expansion point
* `V` – input zonotope
* `R` – start zonotope
* `options` – reachability options
* `step` – linear step

## Hypotheses
* none

## Conclusion
* a successful step encloses every run whose field stays in the input
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- The generator-free zonotope at `v` holds `v`. -/
private theorem aux_oneStep_mem_pt {k : ℕ} (v : Vec 𝕋 k) : -- --- CONCL ---
    toRealVec v ∈ (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 k)).toSet := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩


/-- The inputs of the linearized system when `V` holds the field less its linear part: `V`,
through `B = I`, `c = 0`. -/
private abbrev aux_oneStep_W (A : Mat 𝕋 n n) (V : Zonotope (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  (fun u => Scalar.toRealMat (LinearSys.canonicalFloat A).B *ᵥ u +
    Scalar.toRealVec (LinearSys.canonicalFloat A).c) '' V.toSet

omit [ToRat 𝕋] in
/-- `δ = x - x✱` is a run of the linearized system from `R - x✱` over `[0, T]`, its input in the
image of `V` under `B = I`, `c = 0`. -/
private theorem aux_oneStep_linearize {sys : NonlinearSys n m} {A : Mat 𝕋 n n} {xs : Vec 𝕋 n}
    {V R : Zonotope (Vec 𝕋 n)} {T : ℝ} {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) (Set.Icc 0 T) R.toSet U x u y)
    (hV : ∀ t ∈ Set.Icc 0 T,
      sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ V.toSet) : -- --- CONCL ---
    (LinearSys.canonicalFloat A : LinearSys 𝕋 n).IsCanonicalTrajectory (S := ExactSet)
      (Set.Icc 0 T)
      (R ⊞ (⟨0, (-xs), fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope (Vec 𝕋 n))).toSet
      (aux_oneStep_W A V) (fun t => x t - toRealVec xs) fun t =>
      sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) := by -- --- PROOF ---
  refine traj.linearize_sub measurableSet_Icc ?_ fun t ht => ?_
  -- the start, `R - x✱`
  · have hneg : toRealVec (-xs) = -toRealVec xs := toRealVec_neg _
    have hp := aux_oneStep_mem_pt (-xs)
    rw [hneg] at hp
    have := Plus.plus_outer R (⟨0, (-xs), fun j => j.elim0,
      ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n)) (Set.add_mem_add traj.init hp)
    rwa [← sub_eq_add_neg] at this
  -- the input, through `B = I`, `c = 0`
  · refine ⟨_, hV t ht, ?_⟩
    exact congrFun (LinearSys.canonicalFloat_input A) _

omit [ToRat 𝕋] in
/-- The inputs lie in `V` recentered around `V.c`, a bounded set. -/
private theorem aux_oneStep_recentered (A : Mat 𝕋 n n) (V : Zonotope (Vec 𝕋 n)) :
    (∀ v ∈ aux_oneStep_W A V, v - toRealVec V.c ∈ (Recenter.recenter V).toSet) ∧
      Bornology.IsBounded (aux_oneStep_W A V) := by
  have hid : aux_oneStep_W A V = V.toSet := by
    rw [aux_oneStep_W, LinearSys.canonicalFloat_input, Set.image_id]
  rw [hid]
  exact ⟨fun v hv => Zonotope.sub_center_mem_recenter hv, CompactSet.isBounded_toSet V⟩

omit [ToRat 𝕋] in
/-- Adding `x✱` back to a set holding `y - x✱` gives a set holding `y`. -/
private theorem aux_oneStep_back {xs : Vec 𝕋 n} {Z : Zonotope (Vec 𝕋 n)} {y : Vec ℝ n}
    (hy : y - toRealVec xs ∈ Z.toSet) :
    y ∈ toSet (Z ⊞ (⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 n))) := by
  have := Plus.plus_outer Z (⟨0, xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
    Zonotope (Vec 𝕋 n)) (Set.add_mem_add hy (aux_oneStep_mem_pt xs))
  rwa [sub_add_cancel] at this


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
whose `f(x, u) - A(x - x✱)` stays in `V` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.oneStepFloat_outer {sys : NonlinearSys n m} {A : Mat 𝕋 n n} {xs : Vec 𝕋 n}
    {V R : Zonotope (Vec 𝕋 n)} {options : LinearSys.ReachFloatOptions 𝕋}
    {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ Rτ Rt, (Rτ, Rt) ∈ NonlinearSys.oneStepFloat A xs V R options step →
      0 < toReal options.Δt ∧ ∀ {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
      {y : ℝ → Vec ℝ sys.q},
        sys.IsTrajectory (S := ExactSet) (Set.Icc 0 (toReal options.Δt))
          R.toSet U x u y →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt),
          sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ V.toSet) →
        (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.toSet) ∧
          x (toReal options.Δt) ∈ Rt.toSet := by -- --- PROOF ---
  intro Rτ Rt (hstep : NonlinearSys.oneStepFloat A xs V R options step = some (Rτ, Rt))
  -- every `←` of the step succeeded: name what each returned
  unfold NonlinearSys.oneStepFloat at hstep
  cases step with
  | reachFloatInput =>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨⟨Rti, Rtp⟩, hS, Δτ, hτ, Δ₁, h₁, hpure⟩ := hstep
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  set Δt := options.Δt with hΔt_def
  obtain ⟨hΔt, -⟩ := LinearSys.reachFloatInput_invariant _ _ _ hS
  refine ⟨hΔt, fun {U x u y} traj hV => ?_⟩
  -- the horizon `reachFloatInput` was given is the step
  have hTf : (((ToRat.toRat Δt : ℚ) : ℝ) - ((0 : ℚ) : ℝ)) = toReal Δt := by
    rw [ToRat.toReal_toRat, Rat.cast_zero, sub_zero]
  have ltraj := aux_oneStep_linearize traj hV
  rw [← hTf] at ltraj
  obtain ⟨N, -, hlen, hout⟩ := LinearSys.reachFloatInput_outer _ _ _ hS
  obtain ⟨N', -, -, hout'⟩ := LinearSys.reachFloatInput_timePoint_outer _ _ _ hS
  refine ⟨fun t ht => ?_, ?_⟩
  · cases Rti with
    | nil => simp at hτ
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hτ
      subst hτ
      refine aux_oneStep_back (hout ltraj 0 (by simp) t ⟨by simpa using ht.1, by simpa using ht.2⟩)
  · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h₁
    have := hout' ltraj 1 hk
    rw [Nat.cast_one, one_mul] at this
    exact aux_oneStep_back this
  | closedForm =>
  -- the positive width, and the closed-form step it ran
  dsimp only at hstep
  by_cases hpos : ltStrict (zero : 𝕋) options.Δt = true
  swap
  · simp [hpos] at hstep
  rw [if_pos hpos] at hstep
  have hΔt : 0 < toReal options.Δt := by
    simpa [toReal_zero] using toReal_lt_of_ltStrict hpos
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨S, hS, hpure⟩ := hstep
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  refine ⟨hΔt, fun {U x u y} traj hV => ?_⟩
  have ltraj := aux_oneStep_linearize traj hV
  -- the input is `V.c` and what `V` holds around it, which holds `0`
  obtain ⟨hWU, hW⟩ := aux_oneStep_recentered A V
  -- the closed-form step's theorems, at the window and at its end
  have hη : 2 ≤ max 2 options.η := le_max_left _ _
  have hS' : S ∈ (LinearSys.canonicalFloat A : LinearSys 𝕋 n).oneStepClosedFormFloat _ _ _
      options.Δt (max 2 options.η) := hS
  refine ⟨fun t ht => ?_, ?_⟩
  · exact aux_oneStep_back (ltraj.oneStepClosedFormFloat_timeInterval_outer hη hΔt
      (Zonotope.zero_mem_recenter V) ht.1 ht.2 hWU hW S hS')
  · exact aux_oneStep_back (ltraj.oneStepClosedFormFloat_timePoint_outer hΔt hWU hW S hS')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
