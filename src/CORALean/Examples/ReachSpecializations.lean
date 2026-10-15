import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterConvexCompact
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterConvexCompact
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Linear reachability, one statement per representation

Reachability is stated once, over `ConvexSet` and `CompactSet` and over the
operation classes; these are the per-representation statements it replaced,
kept as use sites. Each is `:=` and nothing else, which is the claim: the
generalization still covers the representation. If one ever stops elaborating,
the generalization has lost it, and this file is where the build says so.

`Zonotope` and `ConZonotope` reach `reach_outer_convexCompact`, so the only
things left to supply are the step, the Taylor order and the bound relating
them.

`Interval` reaches them too, now that it has `Mtimes ℐ` and the two topological
instances. It is the one representation here that has to spell its family out —
`𝒵` and `𝒞` are notation their own `Instances` file declares, and `ℐ` is the
interval *matrix* family, not this one.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- Anonymous, since their content is that they elaborate.

/-- Reachability at a zonotope, with nothing topological left to assume. -/
example {n : ℕ} {sys : LinearSys ℝ n} {T : Set ℝ} {R₀ U : Zonotope (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.IsCanonicalTrajectory (S := 𝒵) T R₀ U x u)
    (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach (S := 𝒵)
      ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  traj.reach_outer_convexCompact hΔt hT η hε ho k

/-- The same at a constrained zonotope, whose compactness comes from its
`domain` being a polytope rather than from the coefficient cube. -/
example {n : ℕ} {sys : LinearSys ℝ n} {T : Set ℝ} {R₀ U : ConZonotope (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.IsCanonicalTrajectory (S := 𝒞) T R₀ U x u)
    (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach (S := 𝒞)
      ⟨R₀, sys.inputSolution (S := 𝒞) Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  traj.reach_outer_convexCompact hΔt hT η hε ho k

/-- The same at an interval, where `reduce` is the identity, so the enclosure
never widens for an order bound and the whole width is the input solution's. -/
example {n : ℕ} {sys : LinearSys ℝ n} {T : Set ℝ} {R₀ U : Interval (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.IsCanonicalTrajectory (S := ℐ𝒱) T R₀ U x u)
    (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach
      (S := ℐ𝒱)
      ⟨R₀, sys.inputSolution (S := ℐ𝒱) Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  traj.reach_outer_convexCompact hΔt hT η hε ho k

/-- The step enclosure at a zonotope: every time of the step, not only its end.
`0 ∈ U` is a fact about where the input set sits, so no class supplies it. -/
example {n : ℕ} {sys : LinearSys ℝ n} {T : Set ℝ} {R₀ U : Zonotope (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.IsCanonicalTrajectory (S := 𝒵) T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep (S := 𝒵) r (m + 2) R₀)
      (sys.inputSolution (S := 𝒵) r (m + 2) U)) :=
  traj.timeInterval_outer_convexCompact hr hT hε ht0 htr h0

/-- The step enclosure at an interval, which is what `Mtimes ℐ` was the last
instance missing for. -/
example {n : ℕ} {sys : LinearSys ℝ n} {T : Set ℝ} {R₀ U : Interval (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory (S := ℐ𝒱) T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus
      (sys.timeIntervalStep (S := ℐ𝒱) r (m + 2) R₀)
      (sys.inputSolution (S := ℐ𝒱) r (m + 2) U)) :=
  traj.timeInterval_outer_convexCompact hr hT hε ht0 htr h0

end CORALean.Real
