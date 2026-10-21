module

public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A time-varying run's whole step, both halves computed from the two sets

`IsTrajectory.timeInterval_outer` with `Vd` named: `sys.inputSolution` at the enlarged set `V`,
extended across the step by the frozen matrix's own `inputReach_mono`, as at `'constParam'`. So
`'varParam'` is enclosed by `'constParam'` at any frozen `Â ∈ construct sys.A`, over an input set
that has absorbed the parameter drift. `V` is the whole price of the time-varying reading, a set
the caller supplies; `IsTrajectory.norm_drift_le` makes it constructible: any `V` containing a
ball of the radius it names will do. `0 ∈ V` buys one enclosure for the whole step rather than
one per time.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `V` – set holding input plus drift
* `x` – trajectory
* `u` – input signal
* `A` – matrix signal
* `r` – step size
* `m` – Taylor order minus two
* `Â` – frozen matrix member
* `t` – time

## Hypotheses
* `traj` – time-varying trajectory
* `hr` – step positive
* `hT` – step lies in the time set
* `hε` – order admissible
* `hÂ` – `Â` lies in the matrix set
* `hV` – drift plus input lies in `V`
* `ht0` – time nonnegative
* `htr` – time at most the step
* `hconv` – `V` convex
* `hclosed` – `V` closed
* `hbdd` – `V` bounded
* `hRconv` – remainder image convex
* `hRclosed` – remainder image closed
* `hRbdd` – remainder image bounded
* `h0` – origin lies in `V`

## Conclusion
* the state at time `t` lies in the step enclosure plus the input solution of `V`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of a `'varParam'` run, initial set and enlarged input together, at
every time of the step. -/
theorem LinParamSys.IsCanonicalTrajectory.timeInterval_outer_inputSolution {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U V : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {Â : Mat ℝ n n} (hÂ : Â ∈ construct sys.A)
    (hV : ∀ s ∈ T, (A s - Â) *ᵥ x s + u s ∈ construct V)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct V)) (hclosed : IsClosed (construct V))
    (hbdd : Bornology.IsBounded (construct V))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) V)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) V)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) V)))
    (h0 : (0 : Vec ℝ n) ∈ construct V) : -- --- CONCL ---
    x t ∈ construct (Plus.plus (sys.timeInterval r (m + 2) R₀)
      (sys.inputSolution r (m + 2) V)) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  -- the frozen matrix names the point system where `inputReach` lives
  have lin := traj.toLinearSys Â hTt measurableSet_Icc fun s hs => hV s (hTt hs)
  have hmemt : (∫ s in (0:ℝ)..t, exp ((t - s) • Â) *ᵥ ((A s - Â) *ᵥ x s + u s))
      ∈ (LinearSys.canonical Â : LinearSys ℝ n).inputReach V t :=
    ⟨fun s => (A s - Â) *ᵥ x s + u s, fun s hs => hV s (hTt hs),
      lin.aestronglyMeasurable_input subset_rfl, by simp only [Scalar.toRealMat_real]⟩
  refine traj.timeInterval_outer hr hT hε hÂ hV hbdd ht0 htr ?_
  exact sys.inputReach_subset_inputSolution hr (m + 2) hε hÂ hconv hclosed hbdd
    hRconv hRclosed hRbdd
    ((LinearSys.canonical Â : LinearSys ℝ n).inputReach_mono hbdd h0 ht0 htr hmemt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
