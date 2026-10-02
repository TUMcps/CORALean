import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputInvariant
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputTimePointOuter
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# One linearized step holds every run whose field it covers

A run of `ẋ = f(x, u)` on `[0, Δt]` from `R` whose `f(x, u) - A(x - x✱)` stays in `V` is,
in `δ = x - x✱`, a run of `δ̇ = A δ + ũ` from `R - x✱` with `ũ ∈ V`.
`reachFloatInput_outer` and its time-point twin place `δ` over the window and at its
end, and adding `x✱` back places `x`. The argument of `relinStepFloat_outer` with
the input set left to the caller.
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
theorem aux_oneStep_mem_pt {k : ℕ} (v : Vec 𝕋 k) :
    toRealVec v ∈ (⟨0, v, fun _ j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope 𝕋 k).construct := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
whose `f(x, u) - A(x - x✱)` stays in `V` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.oneStepFloat_outer {sys : NonlinearSys n m} {A : Mat 𝕋 n n}
    {xs : Vec 𝕋 n} {V R Rτ Rt : Zonotope 𝕋 n} {options : LinearSys.ReachOptions 𝕋}
    (hstep : NonlinearSys.oneStepFloat A xs V R options = some (Rτ, Rt)) :
    0 < toReal options.timeStep ∧ ∀ {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal options.timeStep))
        R.construct U x u →
      (∀ t ∈ Set.Icc 0 (toReal options.timeStep),
        sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs) ∈ V.construct) →
      (∀ t ∈ Set.Icc 0 (toReal options.timeStep), x t ∈ Rτ.construct) ∧
        x (toReal options.timeStep) ∈ Rt.construct := by -- --- PROOF ---
  -- every `←` of the step succeeded: name what each returned
  unfold NonlinearSys.oneStepFloat at hstep
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨⟨Rti, Rtp⟩, hS, Δτ, hτ, Δ₁, h₁, hpure⟩ := hstep
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl⟩ := hpure
  set Δt := options.timeStep with hΔt_def
  obtain ⟨hΔt, -⟩ := LinearSys.reachFloatInput_invariant _ _ hS
  refine ⟨hΔt, fun {U x u} traj hV => ?_⟩
  -- the horizon `reachFloatInput` was given is the step
  have hTf : (((ToRat.toRat Δt : ℚ) : ℝ) - ((0 : ℚ) : ℝ)) = toReal Δt := by
    rw [ToRat.toReal_toRat, Rat.cast_zero, sub_zero]
  -- `δ = x - x✱` is a run of the linearized system from `R - x✱`
  have ltraj : (⟨A⟩ : LinearSys 𝕋 n).Trajectory (S := fun k => Set (Vec ℝ k))
      (Set.Icc 0 (((ToRat.toRat Δt : ℚ) : ℝ) - ((0 : ℚ) : ℝ)))
      (R ⊞ (⟨0, fun i => neg (xs i), fun _ j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope 𝕋 n)).construct
      ((Scalar.toRealMat (identityMat 𝕋 n) *ᵥ ·) '' V.construct)
      (fun t => x t - toRealVec xs)
      (fun t => sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs)) := by
    refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
    -- the start, `R - x✱`
    · have hneg : toRealVec (fun i => neg (xs i)) = -toRealVec xs := by
        funext i; exact toReal_neg (xs i)
      have hp := aux_oneStep_mem_pt (fun i => neg (xs i))
      rw [hneg] at hp
      have := Plus.plus_outer R (⟨0, fun i => neg (xs i), fun _ j => j.elim0,
        ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope 𝕋 n) (Set.add_mem_add traj.init hp)
      rwa [← sub_eq_add_neg] at this
    -- the input, through the identity
    · rw [hTf] at ht
      refine ⟨_, hV t ht, ?_⟩
      funext i
      exact identityMat_mulVec _ i
    -- the flow, `δ̇ = ẋ = A δ + (f - A δ)`
    · have ht' : t ∈ Set.Icc 0 (toReal Δt) := by rwa [hTf] at ht
      have hd := (traj.flow t ht').sub_const (toRealVec xs)
      rw [hTf]
      refine hd.congr_deriv ?_
      show sys.f (x t) (u t) = Scalar.toRealMat A *ᵥ (x t - toRealVec xs)
        + (sys.f (x t) (u t) - Scalar.toRealMat A *ᵥ (x t - toRealVec xs))
      abel
  obtain ⟨N, -, hlen, hout⟩ := LinearSys.reachFloatInput_outer _ _ hS
  obtain ⟨N', -, -, hout'⟩ := LinearSys.reachFloatInput_timePoint_outer _ _ hS
  -- adding `x✱` back
  have hback : ∀ {Z : Zonotope 𝕋 n} {y : Vec ℝ n}, y - toRealVec xs ∈ Z.construct →
      y ∈ construct (Z ⊞ (⟨0, xs, fun _ j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
        Zonotope 𝕋 n)) := fun {Z y} hy => by
    have := Plus.plus_outer Z (⟨0, xs, fun _ j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope 𝕋 n) (Set.add_mem_add hy (aux_oneStep_mem_pt xs))
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
