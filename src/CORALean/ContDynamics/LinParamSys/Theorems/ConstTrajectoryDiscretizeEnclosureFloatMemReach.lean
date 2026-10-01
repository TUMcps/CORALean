import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosureFloat
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

/-!
# A sampled `'constParam'` run lands in the float-sampled system's `reach`

`ConstTrajectory.discretizeEnclosureFloat` handed to `LinParamSysDT.reach_outer`,
as `discretizeEnclosure_mem_reach` is at the exact layer: `reach` at the float
interval-matrix family is the discrete recursion run in floats.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (fun m n => Interval (Mat 𝕋 m n)) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every sample `x (k Δt)` of a `'constParam'` run lies in the float-sampled
system's `reach` after `k` steps under the sampled inputs `Ud`. -/
theorem LinParamSys.ConstTrajectory.discretizeEnclosureFloat_mem_reach
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.mk A : LinearSys ℝ n).stepInput u (toReal Δt) k ∈ construct Ud)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * toReal Δt) ∈ construct ((sys.discretizeEnclosureFloat Δt η).reach ⟨R₀, Ud, 0, k⟩
      ⟨o, ho⟩) :=
  (sys.discretizeEnclosureFloat Δt η).reach_outer ho R₀ Ud
    (traj.discretizeEnclosureFloat hΔt hT hU hUd hη) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
