module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubset
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` contains a run whose linearization is self-consistent

The payoff of `confinement_of_subset`: a caller no longer assumes confinement
of every trajectory, only that each step's computed reachable set lies inside
the region its own certificate was issued for — `hsub`, checkable against the
concrete sets `reach` builds, unlike a hypothesis about `x` itself.

Sound at every `steps` whose regions pass that check, exactly as
`ConPolyZono.reduceBy_outer` is sound at every partition without searching
for one. CORA's enlarge-and-retry search for a region that passes is not
implemented or proved here.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory whose per-step regions pass `hsub`, the
check a caller can actually run against the computed sets. -/
theorem NonlinearSysDT.reach_outer_of_subset (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n)
    (hsub : ∀ k, construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) ⊆ (steps k).R)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.reach_outer ho steps R₀ traj (sys.confinement_of_subset ho steps R₀ hsub traj) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
