import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContDynamics.LinearSys.Operations.Canonical
import CORALean.ContSet.HPolytope.Real.Instances
import CORALean.ContSet.HPolytope.Real.Operations.MemSlabIff
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosureCut
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.Examples.BouncingBall

/-!
# The hybrid-automaton lemmas, at the bouncing ball's types

`BouncingBall`'s automaton, one lemma per example and none of its own: what a run that starts
in an invariant does (stays in it, and meets a requirement checked on it), what a stay in a
location with `LinearSys` dynamics is enclosed by, and what a jump of the ball's `bounce`
is, with the halfspace guard cut down to the zonotope `jump_outer` asks for. Each is
compiled at the ball's representations (`Zonotope` for the state, `HPolytope` for guard and
invariant), so a lemma whose instances stop resolving there fails the build.
-/

-- Authors:       Claude Opus 5
-- Written:       14-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- anonymous, since their content is that they elaborate at this automaton's types

/-- A run that starts inside the invariant ends inside it, however many bounces
it took and wherever it stopped. -/
example (HA : HybridAutomaton 𝒵 ℋ𝒫 Unit ℝ 2) {R : Unit → Zonotope (Vec ℝ 2)}
    (hinv : HA.Invariant R) {ℓ ℓ' : Unit} {x y : Vec ℝ 2} (run : HA.IsRun ℓ x ℓ' y)
    (hx : x ∈ construct (R ℓ)) : y ∈ construct (R ℓ') :=
  run.mem_of_invariant hinv hx

/-- The floor as a requirement rather than as a guard: checked on the invariant
of the location a run ends in, it is answered for the state it ends at. -/
example (HA : HybridAutomaton 𝒵 ℋ𝒫 Unit ℝ 2) {R : Unit → Zonotope (Vec ℝ 2)}
    (hinv : HA.Invariant R) {ℓ ℓ' : Unit} {x y : Vec ℝ 2} (run : HA.IsRun ℓ x ℓ' y)
    (hx : x ∈ construct (R ℓ))
    (h : (Specification.safeSet {z : Vec ℝ 2 | 0 ≤ z 0}).Holds (construct (R ℓ'))) :
    (Specification.safeSet {z : Vec ℝ 2 | 0 ≤ z 0}).Holds {y} :=
  HA.holds_of_invariant hinv _ run hx h

/-- A stay is enclosed by the linear time-interval step, which is what holding
`LinearSys` dynamics in a location buys. -/
example (ℓ : Location 𝒵 ℋ𝒫 Unit ℝ 2) {τ : ℝ} {x : ℝ → Vec ℝ 2} {u w}
    (traj : ℓ.IsTrajectory τ x u w) {R₀ Ud : Zonotope (Vec ℝ 2)}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.inputSet))
    (hUd : (∫ s in (0 : ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ
      (toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s))
      ∈ construct Ud) :
    x t ∈ construct (Plus.plus (ℓ.timeInterval τ (m + 2) R₀) Ud) :=
  traj.timeInterval_outer h₀ hτ hε ht0 htτ hU hUd

/-- The whole point of the separation: a zonotope reachable set, a halfspace
guard, and the reset image once the caller has cut the one down to the other. -/
example (e : Transition ℋ𝒫 Unit ℝ 2) {R Rg : Zonotope (Vec ℝ 2)}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ 2}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump (S := 𝒵) Rg) :=
  e.jump_outer hand hz hguard

/-- The one thing the automaton computes, at the concrete transition: `jump`
needs `Mtimes`, `Plus` and `OfInterval` at `Zonotope` and nothing at `ℋ𝒫`. -/
noncomputable example (d : ℝ) (Rg : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) :=
  (Example.bounce d).jump (S := 𝒵) Rg

end CORALean.Real

