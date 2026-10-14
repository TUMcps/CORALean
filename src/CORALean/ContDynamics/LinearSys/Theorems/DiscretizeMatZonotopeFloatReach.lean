module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotopeFloat
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `discretizeMatZonotopeFloat`'s trajectory lands in `reach`

`discretizeMatZonotopeFloat` handed to `LinParamSysDT.reach_outer`: at the float
matrix-zonotope family, `LinParamSysDT.reach` is the discrete recursion run in floats,
and the sampled continuous run is inside it at every sample time.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (fun m n => Zonotope (Mat 𝕋 m n)) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every sample `x (k Δt)` of a run lies in the float-sampled system's `reach`
after `k` steps under the sampled inputs `Ud`. -/
theorem LinearSys.CanonicalTrajectory.discretizeMatZonotopeFloat_mem_reach {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.CanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u (toReal Δt) k ∈ construct Ud)
    (hε : toReal (MatExp.normUpperBound
      (Zonotope.matSmul Δt Δt (Zonotope.pointMat sys.A)).matInterval) / ((η : ℝ) + 2) ≤ 1 / 2)
    {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * toReal Δt) ∈ construct ((sys.discretizeMatZonotopeFloat Δt η).reach ⟨R₀, Ud, 0, k⟩
      ⟨o, ho⟩) :=
  (sys.discretizeMatZonotopeFloat Δt η).reach_outer ho R₀ Ud
    (traj.discretizeMatZonotopeFloat hΔt hT hU hUd hε) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
