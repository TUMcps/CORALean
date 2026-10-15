module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `discretizeEnclosureFloat`'s trajectory lands in `reach`

`discretizeEnclosureFloat` handed to `LinParamSysDT.reach_outer`, as
`discretizeEnclosure_mem_reach` is at the real layer: at the float
interval-matrix family, `LinParamSysDT.reach` is the discrete recursion run in
floats, and the sampled continuous run is inside it at every sample time.
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

/-- Every sample `x (k Δt)` of a run lies in the float-sampled system's `reach`
after `k` steps under the sampled inputs `Ud`. -/
theorem LinearSys.IsCanonicalTrajectory.discretizeEnclosureFloat_mem_reach {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u (toReal Δt) k ∈ construct Ud)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * toReal Δt) ∈ construct ((sys.discretizeEnclosureFloat Δt η).reach ⟨R₀, Ud, 0, k⟩
      ⟨o, ho⟩) :=
  (sys.discretizeEnclosureFloat Δt η).reach_outer ho R₀ Ud
    (traj.discretizeEnclosureFloat hΔt hT hU hUd hη) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
