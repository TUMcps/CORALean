module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryNormLe

@[expose] public section

/-!
# How large the enlarged input of a frozen step has to be

`IsCanonicalTrajectory.toLinearSys` pays the parameter mismatch into the input, and this is what it
costs: `‖(A t - Â) x t + u t‖`, bounded by the matrix set's radius around `Â` times the Grönwall
bound of the state, plus the input's own bound. Every constant is read off `sys.A`, `U` and `R₀`
before a run is fixed, so a caller can check `hV` of
`IsCanonicalTrajectory.timeInterval_outer_inputSolution` against a ball of this radius. The bound is
taken at the far end of the window, `gronwallBound` being monotone there, so one radius serves the
whole step. `δ` is smallest at the box's center, where it is the box's radius.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `A` – matrix signal
* `a` – window start
* `b` – window end
* `M` – bound on the matrix norm
* `ν` – bound on the input norm
* `ρ` – bound on the start norm
* `δ` – bound on the distance to `Â`
* `Â` – frozen matrix

## Hypotheses
* `traj` – time-varying trajectory
* `hT` – window lies in the time set
* `hM` – matrix norm bounded by `M`
* `hν` – input norm bounded by `ν`
* `hρ` – start norm bounded by `ρ`
* `hδ` – matrix within `δ` of `Â`
* `hδ0` – `δ` nonnegative
* `hM0` – `M` nonnegative
* `hν0` – `ν` nonnegative
* `hρ0` – `ρ` nonnegative

## Conclusion
* drift plus input stays below one radius over the whole window
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One radius for the whole window: the drift plus the input never exceeds
`δ · gronwallBound ρ M ν (b - a) + ν`. -/
theorem LinParamSys.IsCanonicalTrajectory.norm_drift_le {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) {a b : ℝ} (hT : Set.Icc a b ⊆ T)
    {M ν ρ δ : ℝ} (hM : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ M) (hν : ∀ t ∈ Set.Icc a b, ‖u t‖ ≤ ν)
    (hρ : ‖x a‖ ≤ ρ) {Â : Mat ℝ n n} (hδ : ∀ t ∈ Set.Icc a b, ‖A t - Â‖ ≤ δ)
    (hδ0 : 0 ≤ δ) (hM0 : 0 ≤ M) (hν0 : 0 ≤ ν) (hρ0 : 0 ≤ ρ) : -- --- CONCL ---
    ∀ t ∈ Set.Icc a b,
      ‖(A t - Â) *ᵥ x t + u t‖ ≤ δ * gronwallBound ρ M ν (b - a) + ν := by -- --- PROOF ---
  intro t ht
  -- the state's own a priori bound, taken at the far end of the window
  have hx := traj.norm_le hT (fun s hs => hM s (Set.Ico_subset_Icc_self hs))
    (fun s hs => hν s (Set.Ico_subset_Icc_self hs)) hρ t ht
  have hmono : gronwallBound ρ M ν (t - a) ≤ gronwallBound ρ M ν (b - a) :=
    gronwallBound_mono hρ0 hν0 hM0 (by linarith [ht.2])
  refine le_trans (norm_add_le _ _) (add_le_add ?_ (hν t ht))
  refine le_trans (Matrix.linfty_opNorm_mulVec _ _) ?_
  exact mul_le_mul (hδ t ht) (le_trans hx hmono) (norm_nonneg _) hδ0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
