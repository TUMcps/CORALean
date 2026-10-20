module

public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryToLinearSys
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

@[expose] public section

/-!
# A time-varying run stays in the step enclosure, the drift paid as input

`IsConstTrajectory.timeInterval_outer` at `'varParam'`. The homogeneous half is unchanged —
`timeIntervalStep` is the box's and knows no member, so freezing `Â ∈ construct sys.A` costs
nothing there. What changes is the second half: `IsTrajectory.toLinearSys` turns the parameter
mismatch into input, so the set `Vd` has to hold the drift `(A s - Â) x s` as well as `u s`.
This is not CORA's `'varParam'` branch: `Interval.matPow` admits a different member at each
factor, tighter than freezing one; `IsTrajectory.timeIntervalStep_outer` proves *that* set sound
for an input-free run. This is the enclosure freezing gives, sound at every `Â` and with an input.
`Â` is a free choice; the box's center makes the drift smallest.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `V` – set holding input plus drift
* `Vd` – set holding the integrated effect
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
* `hVb` – `V` bounded
* `ht0` – time nonnegative
* `htr` – time at most the step
* `hVd` – integrated effect lies in `Vd`

## Conclusion
* the state at time `t` lies in the step enclosure plus `Vd`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of a `'varParam'` run: the box's homogeneous step, plus whatever
holds the input and the parameter drift together. -/
theorem LinParamSys.IsCanonicalTrajectory.timeInterval_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U V Vd : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {Â : Mat ℝ n n} (hÂ : Â ∈ construct sys.A)
    (hV : ∀ s ∈ T, (A s - Â) *ᵥ x s + u s ∈ construct V)
    (hVb : Bornology.IsBounded (construct V)) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hVd : (∫ s in (0:ℝ)..t, exp ((t - s) • Â) *ᵥ ((A s - Â) *ᵥ x s + u s))
      ∈ construct Vd) : -- --- CONCL ---
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀) Vd) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  -- the run is a point system's run at `Â`, its input enlarged by the drift
  have lin := traj.toLinearSys Â hTt measurableSet_Icc fun s hs => hV s (hTt hs)
  have hvoc := lin.variation_of_constants subset_rfl le_rfl ht0 hVb
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hVd)
  exact sys.timeIntervalStep_outer hr hε R₀ hÂ ht0 htr (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
