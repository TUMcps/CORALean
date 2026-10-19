module

public import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval
public import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

@[expose] public section

/-!
# The re-linearization loop, over the whole of a step rather than its ends

`relinReach_outer_inputSolution` places `x (iΔt)` at the start of step `i`; the
run re-anchored there is a run of the linearized system on `[0, Δt]`, which is
`IsTrajectory.linearize`, and `timeInterval_outer_inputSolution` covers every time
of that run at once. The extra cost beyond the discrete chain is `η ≥ 2` (the
time-interval correction matrix needs it) and `0 ∈ linInput` (`inputReach_mono`'s
own price), neither asked of `relinReach` at all.

`hR` is asked at step `i` itself, not below it, so step `i`'s confinement can
never come from this theorem's own conclusion; `confinement_of_subset` gets it
from the step's start instead.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run confined step by step is inside `relinTimeInterval` at every time of
every step, not only at the step boundaries `relinReach` covers. -/
theorem NonlinearSys.IsTrajectory.relinTimeInterval_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y) (hΔt : 0 < Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (q : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (h0 : ∀ i < N, (0 : Vec ℝ n) ∈ construct (steps i).linInput)
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    {o : ℕ} (ho : 0 < o) (i : ℕ) (hi : i < N)
    {t : ℝ} (ht : t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt)) : -- --- CONCL ---
    x t ∈ construct (sys.relinTimeInterval o ho Δt (q + 2) steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
        (steps i).linInput) R₀ i) := by -- --- PROOF ---
  set Ud : ℕ → S n := fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
    (steps i).linInput with hUd_def
  -- `relinReach_outer_inputSolution` places `x (iΔt)` at the start of step `i`
  have hRi := traj.relinReach_outer_inputSolution hΔt hT hR (q + 2) hε hconv hclosed hbdd
    hRconv hRclosed hRbdd ho i hi.le
  -- the run re-anchored at the start of step `i`, from what `relinReach` encloses there
  have hwin := step_subset_horizon hΔt.le hT hi
  have hexp : ((i : ℝ) + 1) * Δt = (i : ℝ) * Δt + Δt := by ring
  have hmaps : Set.MapsTo (fun s => (i : ℝ) * Δt + s) (Set.Icc (0 : ℝ) Δt) T := by
    intro s hs
    refine hwin ⟨by linarith [hs.1], ?_⟩
    rw [hexp]; linarith [hs.2]
  have shifted := traj.shift hmaps (by simpa using hmaps (Set.left_mem_Icc.2 hΔt.le)) hRi
  have hR1 : ∀ s ∈ Set.Icc (0 : ℝ) Δt, x ((i : ℝ) * Δt + s) ∈ (steps i).R := by
    intro s hs
    refine hR i hi _ ⟨by linarith [hs.1], ?_⟩
    rw [hexp]; linarith [hs.2]
  -- the shifted run is a run of the linearized system, on `[0, Δt]`
  have hlin := shifted.linearize measurableSet_Icc (steps i).cert hR1
  -- `t`'s own position inside the step, re-anchored the same way
  set s := t - (i : ℝ) * Δt with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; linarith [ht.1]
  have hsΔt : s ≤ Δt := by rw [hs_def]; nlinarith [ht.2, hexp]
  have hbeta : (i : ℝ) * Δt + s = t := by rw [hs_def]; ring
  have key := hlin.timeInterval_outer_inputSolution hΔt subset_rfl (m := q) (hε i hi) hs0 hsΔt
    (hconv i hi) (hclosed i hi) (hbdd i hi) (hRconv i hi) (hRclosed i hi) (hRbdd i hi) (h0 i hi)
  show x t ∈ construct (Plus.plus ((NonlinearSys.linearize (steps i).A).timeIntervalStep Δt
    (q + 2) (sys.relinReach ⟨R₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud)) (Ud i))
  rw [← hbeta]
  exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
