module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the reachable set holds along every trajectory

`LinearSysDT.holds_of_reach`'s statement, at a re-linearized step: `reach_outer`
handed to `Specification.holds_of_outer`, so the linearization `steps` and its
confinement hypothesis `hR` are threaded through unchanged rather than hidden
behind a weaker statement. `holds_of_reach_of_subset` is the same corollary
from `hsub`, the check a caller can run against the computed sets instead.

## Inputs
* `sys` – system
* `U` – input set
* `o` – maximum order
* `steps` – linearization steps
* `R₀` – initial set
* `spec` – specification
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `k` – step

## Hypotheses
* `ho` – order positive
* `traj` – trajectory of the system
* `hR` – states stay in regions
* `h` – specification holds on the reachable set

## Conclusion
* the specification holds on the state
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.holds_of_reach (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) (spec : Specification ContSet)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} {y : ℕ → Vec ℝ sys.q} (traj : sys.IsTrajectory R₀ U x u y)
    (hR : ∀ k, x k ∈ (steps k).R) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps))) : -- --- CONCL ---
    spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer ho steps R₀ traj hR k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
