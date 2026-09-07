import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosureCut
import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# A bouncing ball, as a hybrid automaton

The textbook automaton: one location, one transition back into it. The state is
`(position, velocity)`, the dynamics are `ṗ = v`, `v̇ = -g` written as a constant
input, `LinearSys` having no offset. The guard is the floor met from above, and
the reset flips the velocity and damps it by `d`. The invariant is a box, so
`Zonotope` supplies every instance the pipeline asks for: `Mtimes` and `Plus` for
the reset image, `LinComb` and `Mtimes ℐ` for the stay.

What the automaton cannot say is the interface's shape, not this example's: the
guard is a *bounded* set, the floor met at a speed of at most `v`, since a
location's sets share one representation and a zonotope cannot be the halfspace
`p = 0 ∧ v ≤ 0` — which `HPolytope` states and still cannot jump from.

`Zonotope` has no `And` instance still, so `timeIntervalStepInv` and `jumpAnd`
stay out of reach; `InvariantOfEnclosureCut` needs neither, cutting with `ℓ.inv`
and with the guard as set inclusions, which is what lets
`bouncingBall_invariant` discharge it at the location's own invariant.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The bounce: on the floor with a downward speed of at most `v`, keep the
position and reverse the velocity, damped by `d`. -/
noncomputable def Example.bounce (d v : ℝ) : Transition 𝒵 Unit ℝ 2 where
  guard := ⟨1, ![0, -v / 2], ![![0, v / 2]]⟩
  W := !![1, 0; 0, -d]
  w := 0
  target := ()


-- =====================================  MAIN DEFINITION  ====================================== --

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
example (e : Transition 𝒵 Unit ℝ 2) {R Rg : Zonotope (Vec ℝ 2)}
    (hand : construct R ∩ construct e.guard ⊆ construct Rg) {z : Vec ℝ 2}
    (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jump Rg) :=
  e.jump_outer hand hz hguard

/-- The one thing the automaton computes, at the concrete transition: `jump`
needs `Mtimes`, `Plus` and `OfInterval` all at `Zonotope`. -/
noncomputable example (d v : ℝ) (Rg : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) :=
  (Example.bounce d v).jump Rg

/-- The reset image of the guard, in coordinates: the floor, left with an
upward velocity of at most `d v`. -/
theorem Example.mem_bounce_jump_guard {d v : ℝ} {x : Vec ℝ 2}
    (hx : x ∈ construct ((Example.bounce d v).jump (Example.bounce d v).guard)) :
    ∃ s : ℝ, |s| ≤ 1 ∧ x = ![0, d * v / 2 - d * v / 2 * s] := by -- --- PROOF ---
  replace hx : x ∈ (Zonotope.mtimes (Example.bounce d v).W (Example.bounce d v).guard).construct
      + ((Interval.point (toRealVec (Example.bounce d v).w)).zonotope).construct := by
    rw [Zonotope.plus_exact]; exact hx
  rw [← Zonotope.mtimes_exact] at hx
  obtain ⟨a, ⟨z, ⟨β, hβ, rfl⟩, rfl⟩, b, ⟨γ, -, rfl⟩, rfl⟩ := hx
  refine ⟨β ⟨0, Nat.zero_lt_one⟩, hβ _, ?_⟩
  funext i
  fin_cases i
  · simp [Example.bounce, Interval.point, Interval.zonotope]
  · simp [Example.bounce, Interval.point, Interval.zonotope]
    ring

/-- The criterion at this automaton: the location's own invariant is an
inductive invariant, the flow half discharged by the cut and the jump half by
the damping being at most one. -/
theorem Example.bouncingBall_invariant (g p v : ℝ) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (Example.bouncingBall g d p v).Invariant
      (fun ℓ => ((Example.bouncingBall g d p v).loc ℓ).inv) := by -- --- PROOF ---
  refine HybridAutomaton.invariant_of_enclosure_cut _ _ (fun ℓ τ _ => ?_) (fun ℓ e he => ?_)
  · -- the cut is the whole flow obligation: whatever the dwell time, the part
    -- of the enclosure still inside the invariant is inside the invariant
    refine ⟨⌈‖τ • toRealMat ((Example.bouncingBall g d p v).loc ℓ).dynamics.A‖⌉₊, ?_,
      Set.inter_subset_right⟩
    rw [div_lt_one (by positivity)]
    push_cast
    linarith [Nat.le_ceil ‖τ • toRealMat ((Example.bouncingBall g d p v).loc ℓ).dynamics.A‖]
  · -- the bounce is the only transition, its own guard the enclosure `jump_outer`
    -- asks for, and the reset image sits in the box exactly when `d ≤ 1`
    simp only [Example.bouncingBall, List.mem_singleton] at he
    subst he
    refine ⟨(Example.bounce d v).guard, Set.inter_subset_right, fun x hx => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Example.mem_bounce_jump_guard hx
    rw [abs_le] at hs
    show _ ∈ Zonotope.construct (⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩ : Zonotope (Vec ℝ 2))
    refine ⟨![-1, d * (1 - s) / 2], Fin.forall_fin_two.2 ⟨by simp, ?_⟩, ?_⟩
    · show |d * (1 - s) / 2| ≤ 1
      rw [abs_le]
      constructor <;> nlinarith [hs.1, hs.2]
    · funext i
      fin_cases i
      · simp [Fin.sum_univ_two]
      · simp [Fin.sum_univ_two]
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
