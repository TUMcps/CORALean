import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# A bouncing ball, as a hybrid automaton

The textbook automaton: one location, one transition back into it. The state is
`(position, velocity)`, the dynamics are `ṗ = v`, `v̇ = -g` written as a constant
input, `LinearSys` having no offset. The guard is the floor met from above, and
the reset flips the velocity and damps it by `d`. The invariant is a box, so
`Zonotope` supplies every instance the pipeline asks for: `Mtimes` and `Plus` for
the reset image, `LinComb` and `Mtimes ℐ` for the stay.

Two things the automaton cannot say, and they are the interface's shape rather
than this example's. The guard is a *bounded* set — the floor met with a speed of
at most `v` — because a location's sets share one representation and a zonotope
cannot be the halfspace `p = 0 ∧ v ≤ 0`; `HPolytope` states that halfspace and
still cannot take the jump, computing `Plus` only on named directions.

And nothing here intersects: `Location.inv` is data the automaton carries and no
theorem cuts a reachable set down with it, as `Transition.guard` is only ever
tested pointwise. Both are the missing `And` interface.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The bounce: on the floor with a downward speed of at most `v`, keep the
position and reverse the velocity, damped by `d`. -/
noncomputable def Example.bounce (d v : ℝ) : Transition 𝒵 Unit 2 where
  guard := ⟨1, ![0, -v / 2], ![![0, v / 2]]⟩
  W := !![1, 0; 0, -d]
  w := 0
  target := ()

/-- Falling under gravity inside the box `[0, p] × [-v, v]`, and bouncing out of
the only location back into it. -/
noncomputable def Example.bouncingBall (g d p v : ℝ) : HybridAutomaton 𝒵 Unit ℝ 2 where
  loc _ :=
    { inv := ⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩
      dynamics := ⟨!![0, 1; 0, 0]⟩
      U := ⟨0, ![0, -g], ![]⟩
      trans := [Example.bounce d v] }

-- anonymous, since their content is that they elaborate at this automaton's types

/-- A run that starts inside the invariant ends inside it, however many bounces
it took and wherever it stopped. -/
example (HA : HybridAutomaton 𝒵 Unit ℝ 2) {R : Unit → Zonotope (Vec ℝ 2)}
    (hinv : HA.Invariant R) {ℓ ℓ' : Unit} {x y : Vec ℝ 2} (run : HA.Run ℓ x ℓ' y)
    (hx : x ∈ construct (R ℓ)) : y ∈ construct (R ℓ') :=
  run.mem_of_invariant hinv hx

/-- The floor as a requirement rather than as a guard: checked on the invariant
of the location a run ends in, it is answered for the state it ends at. -/
example (HA : HybridAutomaton 𝒵 Unit ℝ 2) {R : Unit → Zonotope (Vec ℝ 2)}
    (hinv : HA.Invariant R) {ℓ ℓ' : Unit} {x y : Vec ℝ 2} (run : HA.Run ℓ x ℓ' y)
    (hx : x ∈ construct (R ℓ))
    (h : (Specification.safeSet {z : Vec ℝ 2 | 0 ≤ z 0}).Holds (construct (R ℓ'))) :
    (Specification.safeSet {z : Vec ℝ 2 | 0 ≤ z 0}).Holds {y} :=
  HA.holds_of_invariant hinv _ run hx h

/-- A stay is enclosed by the linear time-interval step, which is what holding
`LinearSys` dynamics in a location buys. -/
example (ℓ : Location 𝒵 Unit ℝ 2) {τ : ℝ} {x u : ℝ → Vec ℝ 2}
    (traj : ℓ.Trajectory τ x u) {R₀ Ud : Zonotope (Vec ℝ 2)}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.U))
    (hUd : (∫ s in (0 : ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ u s)
      ∈ construct Ud) :
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀) Ud) :=
  traj.timeInterval_outer h₀ hτ hε ht0 htτ hU hUd

/-- The reset image, once the caller has cut the incoming set down to the
guard. -/
example (e : Transition 𝒵 Unit 2) {R Rg : Zonotope (Vec ℝ 2)}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ 2}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump Rg) :=
  e.jump_outer hand hz hguard

/-- The one thing the automaton computes, at the concrete transition: `jump`
needs `Mtimes`, `Plus` and `OfInterval` all at `Zonotope`. -/
noncomputable example (d v : ℝ) (Rg : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) :=
  (Example.bounce d v).jump Rg

end CORALean.Real
