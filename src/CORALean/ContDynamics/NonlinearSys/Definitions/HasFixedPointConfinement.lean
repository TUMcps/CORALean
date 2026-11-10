module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Confinement by the abstraction error's fixed point

What CORA's abstraction-error loop relies on ("loop until the actual abstraction error is smaller
than the estimated abstraction error"), as a property of the system: if a set `K` holds every run
on `[0, Δt]` from `R` of *any* system whose field less `A (x - x✱)` stays in `V`, and the field of
`sys` less `A (x - x✱)` lies in `V` on `K`, then every run of `sys` stays in `K`. For a field
locally Lipschitz in the state it follows from Picard's iteration (each iterate is a run of the
linear system with input in `V`, so in `K`, and they converge to the run); without regularity it can
fail (`ẋ = 3|x|^{2/3}`, `K = {0}`). Not proved here: the adaptive theorems take it as a hypothesis.

## Inputs
* `sys` – system

## Output
* whether the fixed point of the abstraction error confines the runs of `sys`
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A set holding every run of every system dominated by the linear step with input `V` holds
every run of `sys`, once the field of `sys` less `A (x - x✱)` lies in `V` on the set. -/
def NonlinearSys.HasFixedPointConfinement (sys : NonlinearSys n m) : Prop :=
  ∀ (Δt : ℝ) (R V K : Set (Vec ℝ n)) (U : Set (Vec ℝ m)) (A : Mat ℝ n n) (xs : Vec ℝ n),
    (∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
        (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
        sys'.IsTrajectory (S := 𝒮) (Set.Icc 0 Δt) R U' x' u' y' →
        (∀ t ∈ Set.Icc 0 Δt, sys'.f (x' t) (u' t) - A *ᵥ (x' t - xs) ∈ V) →
        ∀ t ∈ Set.Icc 0 Δt, x' t ∈ K) →
    (∀ y ∈ K, ∀ v ∈ U, sys.f y v - A *ᵥ (y - xs) ∈ V) →
    ∀ (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) (y : ℝ → Vec ℝ sys.q),
      sys.IsTrajectory (S := 𝒮) (Set.Icc 0 Δt) R U x u y → ∀ t ∈ Set.Icc 0 Δt, x t ∈ K

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
