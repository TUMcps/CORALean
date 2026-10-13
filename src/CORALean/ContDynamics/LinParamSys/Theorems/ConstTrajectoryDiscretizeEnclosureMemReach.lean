module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryDiscretizeEnclosure
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# A sampled constant-parameter run lands in `reach`, over a whole horizon

The loop of [1, Alg. 4]: `discretizeEnclosure` handed to
`LinParamSysDT.reach_outer`, so the whole run — propagate by the enclosed
exponential, add the input set, reduce — is the discrete recursion and the
continuous guarantee holds at every sample time `k Δt`, for every `k`.

`reduce` enters here and nowhere else, which is what makes this algorithm the
one of [1] that is *not* wrapping-effect free: each step multiplies the previous
set by an interval matrix and reduces the result, rather than propagating the
initial set by one exact exponential.

No horizon is fixed. `[1, Alg. 4]` runs `k = 1 … t_f/r` and takes the union;
`k` is universally quantified here instead, so a bounded horizon is a
restriction of this rather than a second statement.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sampling into the discretized system and then running its recursion: the
reachable set at every sample time, at maximum order `o`. -/
theorem LinParamSys.ConstTrajectory.discretizeEnclosure_mem_reach {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.mk A : LinearSys ℝ n).stepInput u Δt k ∈ construct Ud)
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretizeEnclosure Δt η).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  (sys.discretizeEnclosure Δt η).reach_outer ho R₀ Ud
    (traj.discretizeEnclosure hΔt hT hU hUd hε) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
