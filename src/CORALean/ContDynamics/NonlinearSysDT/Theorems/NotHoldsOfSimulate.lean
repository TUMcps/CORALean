module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_isTrajectory`, exactly
`LinearSysDT.not_holds_of_simulate`'s statement at a re-linearized step: a
specification violated along one sampled run cannot have held on the
reachable set either. Confinement (`hR`) is asked of `simulate` itself, as
`simulate_mem_reach` already asks it — no shortcut around checking a sampled
run stayed in the region each step's certificate was issued for.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
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
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.not_holds_of_simulate (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) (spec : Specification ContSet)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ m} (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, sys.simulate x₀ u k ∈ (steps k).R) (k : ℕ)
    (hbad : ¬ spec.Holds {sys.simulate x₀ u k}) : -- --- STMT ---
    ¬ spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps)) :=
  fun h => hbad (sys.holds_of_reach ho steps R₀ spec (sys.simulate_isTrajectory hx₀ hu) hR k h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
