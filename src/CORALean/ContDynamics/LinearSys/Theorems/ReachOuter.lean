module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Theorems.Discretize
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` contains every trajectory at the sample times

The whole proof is `Discretize` handed to `LinearSysDT.reach_outer`: once a
sampled run is a discrete run, the discrete guarantee is the continuous one at
`0, Δt, 2Δt, ...`. Between the sample times it says nothing — that is
`TimeIntervalOuter`.

`Mtimes (Mat ℝ) S`, not `Mat 𝕋`: the propagated matrix is `e^{AΔt}`, which is
real whatever the system stores.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- Sampling and then running the discrete-time recursion; nothing here
combines, which is why `LinComb` is not asked for. -/
theorem LinearSys.CanonicalTrajectory.reach_outer {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.CanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  LinearSysDT.reach_outer _ ho R₀ Ud (traj.discretize hΔt hT hU hUd) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
