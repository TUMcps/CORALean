import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

/-!
# The nonlinear reachable set is the linearized one

The payoff: nothing new is computed for a nonlinear system. Once `linearize` has
turned the run into a linear one, `LinearSys.Trajectory.reach_outer` is the whole
proof and the enclosing set is the linear system's `reach`.

The nonlinearity is paid for entirely in `linInput`, which is why the statements
below differ from their linear counterparts only in that `U` has been widened and
a confinement hypothesis added. `exp` needs a norm on `Mat` — a choice, not an
instance — and it is the `l∞` operator norm here as everywhere `discretize` is.

`reach_outer` leaves the discrete input set to the caller;
`reach_outer_inputSolution` names it, and is the statement with no trajectory
left in it. Its price is that `linInput` has to be convex, closed and bounded.

The first two sample all of forward time and ask confinement of it too. The
`_horizon` pair asks for `[0, KΔt]` and concludes about the sample times inside
it: one linearization, one horizon, and a fresh certificate after that.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]

/-- A confined nonlinear run is inside the linearized system's reachable set at
every sample time. -/
theorem NonlinearSys.Trajectory.reach_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ Ud L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {R : Set (Vec ℝ n)} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys A B xs us R (construct U) L)
    (hT : Set.Ici 0 ⊆ T) (hR : ∀ t : ℝ, 0 ≤ t → x t ∈ R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct (sys.linInput A B xs us U L)))
    (hUd : ∀ k : ℕ, (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach o R₀ Ud k) :=
  ((traj.restrict hT).linearize cert hR).reach_outer hΔt subset_rfl hU hUd o k

/-- The same with the input enclosure named, so no quantity depending on the
trajectory survives into the hypotheses. -/
theorem NonlinearSys.Trajectory.reach_outer_inputSolution [Mtimes ℐ S]
    {sys : NonlinearSys n m} {T : Set ℝ} {R₀ L : S n} {U : S m} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n}
    {us : Vec ℝ m} {R : Set (Vec ℝ n)} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys A B xs us R (construct U) L)
    (hT : Set.Ici 0 ⊆ T) (hR : ∀ t : ℝ, 0 ≤ t → x t ∈ R) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct (sys.linInput A B xs us U L)))
    (hclosed : IsClosed (construct (sys.linInput A B xs us U L)))
    (hbdd : Bornology.IsBounded (construct (sys.linInput A B xs us U L)))
    -- the next three are asked of the remainder's product, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L))))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L))))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L)))) (o k : ℕ) :
    x (k * Δt) ∈ construct (((NonlinearSys.linearize A).discretize Δt).reach o R₀
      ((NonlinearSys.linearize A).inputSolution Δt η
        (sys.linInput A B xs us U L)) k) :=
  ((traj.restrict hT).linearize cert hR).reach_outer_inputSolution hΔt subset_rfl η hε
    hconv hclosed hbdd hRconv hRclosed hRbdd o k

/-- The one-step statement: confinement on `[0, KΔt]` alone puts the run inside
the linearized reachable set at every sample time of that horizon, assuming
nothing past `KΔt` — which is what re-linearizing from there needs. -/
theorem NonlinearSys.Trajectory.reach_outer_horizon {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ Ud L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {R : Set (Vec ℝ n)} {Δt : ℝ} {K : ℕ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys A B xs us R (construct U) L)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) ((K : ℝ) * Δt), x t ∈ R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct (sys.linInput A B xs us U L)))
    (hUd : ∀ k < K, (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt k ∈ construct Ud) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈
      construct (((NonlinearSys.linearize A).discretize Δt).reach o R₀ Ud k) :=
  (traj.linearize_horizon cert hT hR).reach_outer_horizon hΔt subset_rfl hU hUd o

/-- The same with the input enclosure named, so no quantity depending on the
trajectory survives into the hypotheses. -/
theorem NonlinearSys.Trajectory.reach_outer_horizon_inputSolution [Mtimes ℐ S]
    {sys : NonlinearSys n m} {T : Set ℝ} {R₀ L : S n} {U : S m} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n}
    {us : Vec ℝ m} {R : Set (Vec ℝ n)} {Δt : ℝ} {K : ℕ} (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys A B xs us R (construct U) L)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) ((K : ℝ) * Δt), x t ∈ R) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct (sys.linInput A B xs us U L)))
    (hclosed : IsClosed (construct (sys.linInput A B xs us U L)))
    (hbdd : Bornology.IsBounded (construct (sys.linInput A B xs us U L)))
    -- the next three are asked of the remainder's product, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L))))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L))))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (sys.linInput A B xs us U L)))) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct
      (((NonlinearSys.linearize A).discretize Δt).reach o R₀
        ((NonlinearSys.linearize A).inputSolution Δt η
          (sys.linInput A B xs us U L)) k) :=
  (traj.linearize_horizon cert hT hR).reach_outer_horizon_inputSolution hΔt subset_rfl η hε
    hconv hclosed hbdd hRconv hRclosed hRbdd o

end CORALean.Real
