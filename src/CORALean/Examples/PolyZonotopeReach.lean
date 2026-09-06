import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# Linear reachability on a non-convex representation

What this records is a fact about the library rather than about any system:
`LinearSysDT.reach` asks for `Plus`, `Reduce` and `Mtimes` and for nothing else,
and `PolyZonotope` now has all three. `Reduce` was the one it was missing, so
the sampled reachability guarantee runs at a representation whose sets are
generally *not* convex — no `ConvexSet`, no `CompactSet`, and none needed.

That is why the plain `reach_outer` is the statement here and not
`reach_outer_convexCompact`: the input contribution arrives as the hypothesis
`hUd` rather than from `inputSolution`, which is the trade a non-convex
representation makes. Discharging it needs `Mtimes ℐ`, an interval matrix acting
on a polynomial zonotope, which no instance supplies.

The Lean detail is `FeedForward.lean`'s: `S : ℕ → Type` cannot be read off `S n`,
so a use site has to name the family, and `PolyZonotope` ships `𝒫𝒵` for that. It
names the family and not the binders — a notation is a lambda, and `𝒫𝒵 n` left
standing will not unify against a metavariable applied to `n`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- Every trajectory of a linear system whose sets are polynomial zonotopes lies
in `reach` at each sample time. It fails to compile the moment `PolyZonotope`
loses one of the three instances the discrete recursion propagates through. -/
example {n : ℕ} (sys : LinearSys ℝ n) (T : Set ℝ) (R₀ U Ud : PolyZonotope (Vec ℝ n))
    (x u : ℝ → Vec ℝ n) (Δt : ℝ) (traj : sys.Trajectory (S := 𝒫𝒵) T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach (S := 𝒫𝒵) o R₀ Ud k) :=
  traj.reach_outer hΔt hT hU hUd o k

/-- The bounded-horizon form, which is what a hybrid location could call: the
domain covers `[0, KΔt]` and the conclusion stops at step `K`. -/
example {n : ℕ} (sys : LinearSys ℝ n) (T : Set ℝ) (R₀ U Ud : PolyZonotope (Vec ℝ n))
    (x u : ℝ → Vec ℝ n) (Δt : ℝ) (K : ℕ) (traj : sys.Trajectory (S := 𝒫𝒵) T R₀ U x u)
    (hΔt : 0 ≤ Δt) (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct ((sys.discretize Δt).reach (S := 𝒫𝒵) o R₀ Ud k) :=
  traj.reach_outer_horizon hΔt hT hU hUd o

end CORALean.Real
