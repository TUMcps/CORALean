module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryDiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A sampled `'constParam'` run lands in the float-sampled system's `reach`

`IsConstTrajectory.discretizeEnclosureFloat` handed to `LinParamSysDT.reach_outer`,
as `discretizeEnclosure_mem_reach` is at the exact layer: `reach` at the float
interval-matrix family is the discrete recursion run in floats.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `Ud` – set of sampled inputs
* `x` – trajectory
* `u` – input signal
* `A` – system matrix member
* `Δt` – sampling time
* `η` – Taylor order
* `o` – maximum zonotope order
* `k` – number of steps

## Hypotheses
* `traj` – constant-parameter trajectory
* `hΔt` – sampling time nonnegative
* `hT` – nonnegative times lie in the time set
* `hU` – input set bounded
* `hUd` – sampled inputs lie in `Ud`
* `hη` – order admissible
* `ho` – order positive

## Conclusion
* the sample after `k` steps lies in the float-sampled system's reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes ℐ[𝕋] S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every sample `x (k Δt)` of a `'constParam'` run lies in the float-sampled
system's `reach` after `k` steps under the sampled inputs `Ud`. -/
theorem LinParamSys.IsCanonicalConstTrajectory.discretizeEnclosureFloat_mem_reach
    {sys : LinParamSys ℐ[𝕋] n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.canonical A : LinearSys ℝ n).stepInput u (toReal Δt) k ∈ construct
        Ud)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ} (ho : 0 < o) (k : ℕ) : -- --- CONCL ---
    x (k * toReal Δt) ∈ construct ((sys.discretizeEnclosureFloat Δt η).reach ⟨R₀, Ud, 0, k⟩
      ⟨o, ho⟩) :=
  (sys.discretizeEnclosureFloat Δt η).reach_outer ho R₀ Ud
    (traj.discretizeEnclosureFloat hΔt hT hU hUd hη) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
