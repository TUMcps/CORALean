module

public import CORALean.ContDynamics.LinearSys.Theorems.DeltaReachOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

@[expose] public section

/-!
# A run's state difference over a step lies in `deltaReach`

CORA's `Rdelta = Rhom + RV`, and the guarantee that makes it usable: the difference `x(t) - x(0)`
between a state of the step and the state the step started from, at every `t` of `[0, r]` and not
only at its ends. The closed form splits the difference the same way it splits the state, into what
the initial set carries and what the inputs contributed, and the *same* input enclosure serves both,
the integral being unchanged by subtracting `x(0)`. So a caller already discharging `hUd` for
`timeInterval_outer` pays nothing more. Integrability is not a hypothesis; `InputIntegrable` derives
it from `U` being bounded.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `Ud` – set holding the input integral
* `x` – state trajectory
* `u` – input signal
* `r` – step length
* `m` – Taylor order offset
* `t` – time

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hr` – step length positive
* `hT` – step lies in the time domain
* `hε` – scaled norm small enough for the Taylor order
* `ht0` – time nonnegative
* `htr` – time within the step
* `hU` – input set bounded
* `hUd` – input integral lies in its set

## Conclusion
* the state difference lies in the delta reach set plus the input set
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step and nothing more, on the differences: the domain has to cover
`[0, r]` only, which is what makes this a statement about a single
linearization step rather than about a whole run. -/
theorem LinearSys.IsCanonicalTrajectory.deltaReach_outer {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.IsCanonicalTrajectory T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) ∈ construct Ud) :
    x t - x 0 ∈ construct (Plus.plus (sys.deltaReach r (m + 2) R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hvoc := traj.variation_of_constants hTt le_rfl ht0
    hU
  rw [sub_zero] at hvoc
  -- subtracting the step's own start leaves the initial state's term a difference
  have hsplit : x t - x 0
      = (exp (t • toRealMat sys.A) *ᵥ x 0 - x 0)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s := by
    rw [hvoc]; abel
  rw [hsplit]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.deltaReach_outer hr hε R₀ ht0 htr (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
