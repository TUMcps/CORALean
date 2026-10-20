module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

@[expose] public section

/-!
# A run over a window, re-anchored, as a linear run

`linearize` hands a run to `linearize A` on the run's own clock, the integral equation anchored at
`0`. A step `[t₀, t₀ + τ]` of a longer run is re-anchored at its start first (`shift`): the state
`x (t₀ + t)` and the input `ũ(t) = f(x(t₀+t), u(t₀+t)) - A x(t₀+t)` are then a run of `ẋ = A x + ũ`
on `[0, τ]` from the point `x t₀`, with `ũ` in any set `V` holding it over the step. The sets are
plain sets, `(S := 𝒮)`: the point and `V` are what the step knows, whatever the representation the
run's own sets are in, and every `LinearSys` guarantee is generic in it.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `A` – state matrix
* `V` – input set
* `t₀` – window start
* `τ` – window length
* `y` – output trajectory

## Hypotheses
* `traj` – trajectory of the system
* `hτ` – window length nonnegative
* `hT` – window inside time set
* `hV` – remainder inputs in input set

## Conclusion
* the re-anchored window is a linear trajectory
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `[t₀, t₀ + τ]` of a run, re-anchored at `t₀`, is a run of `linearize A` from `x t₀`
under an input in `V`. -/
theorem NonlinearSys.IsTrajectory.linearize_window {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {V : Set (Vec ℝ n)} {t₀ τ : ℝ} {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y)
    (hτ : 0 ≤ τ)
    (hT : Set.Icc t₀ (t₀ + τ) ⊆ T)
    (hV : ∀ t ∈ Set.Icc t₀ (t₀ + τ), sys.f (x t) (u t) - A *ᵥ x t ∈ V) : -- --- CONCL ---
    (NonlinearSys.linearize A).IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 τ) {x t₀} V
      (fun t => x (t₀ + t))
      (fun t => sys.f (x (t₀ + t)) (u (t₀ + t)) - A *ᵥ x (t₀ + t)) := by -- --- PROOF ---
  have hmaps : Set.MapsTo (fun t => t₀ + t) (Set.Icc 0 τ) T :=
    fun t ht => hT ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have traj' : sys.IsTrajectory (S := 𝒮) T (construct R₀) (construct U) x u y :=
    ⟨traj.init, traj.input, traj.meas, traj.integrable, traj.cont, traj.flow, traj.output⟩
  have shifted := traj'.shift (R₀' := ({x t₀} : Set (Vec ℝ n))) hmaps
    (hT ⟨le_rfl, by linarith⟩) rfl
  refine ⟨shifted.init, fun t ht => hV _ ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    shifted.meas.sub (((mulVecL A).continuous.comp_continuousOn shifted.cont).aestronglyMeasurable
      measurableSet_Icc), shifted.cont, fun t ht => ?_⟩
  have he : (fun s => toRealMat (NonlinearSys.linearize A).A *ᵥ x (t₀ + s)
      + (sys.f (x (t₀ + s)) (u (t₀ + s)) - A *ᵥ x (t₀ + s)))
      = fun s => sys.f (x (t₀ + s)) (u (t₀ + s)) := by
    funext s
    show A *ᵥ x (t₀ + s) + (sys.f (x (t₀ + s)) (u (t₀ + s)) - A *ᵥ x (t₀ + s)) = _
    abel
  rw [he]
  exact shifted.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
