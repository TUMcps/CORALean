module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn

@[expose] public section

/-!
# Confinement, discharged from the computed sets

`reach_outer_on` asks for confinement (`x j ∈ (steps j).R`) at every step strictly *below* `K`
to place `x K`, never at `K` itself. That asymmetry makes this theorem possible without
circularity: strong induction on `k` gets confinement below `k` from the hypothesis, places
`x k` inside `reach ... k` by `reach_outer_on`, and `hsub k` turns that placement into
confinement *at* `k`. `hsub` is a hypothesis about sets, not a decision procedure; what changes
is *what* a caller must establish, a checkable property of the computed enclosures rather than
of every trajectory. CORA also *enlarges* the candidate region on failure and retries; that
search owes no proof here, and none is implemented.

## Inputs
* `sys` – system
* `U` – input set
* `o` – maximum order
* `steps` – linearization steps
* `R₀` – initial set
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `k` – step

## Hypotheses
* `ho` – order positive
* `hsub` – computed sets inside regions
* `traj` – trajectory of the system

## Conclusion
* the state at the step lies in its certified region
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

/-- Confinement at every step, discharged from the computed sets: a caller
checks `hsub`, that each step's computed reachable set lies inside its own
certified region, instead of assuming confinement of the trajectory. -/
theorem NonlinearSysDT.confinement_of_subset (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n)
    (hsub : ∀ k, construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) ⊆ (steps k).R)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} {y : ℕ → Vec ℝ sys.q} (traj : sys.IsTrajectory R₀ U x u y)
    (k : ℕ) : -- --- CONCL ---
    x k ∈ (steps k).R := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hOn : sys.IsTrajectoryOn R₀ U k x u y :=
      ⟨traj.init, fun j _ => traj.input j, fun j _ => traj.step j, fun j _ => traj.output j⟩
    exact hsub k (sys.reach_outer_on ho steps R₀ hOn ih k le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
