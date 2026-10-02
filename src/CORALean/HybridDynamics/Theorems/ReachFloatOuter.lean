import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.HybridDynamics.Definitions.RunUntil
import CORALean.HybridDynamics.Operations.ReachFloat
import CORALean.HybridDynamics.Theorems.GuardIntersectFloatOuter
import CORALean.HybridDynamics.Theorems.JumpFloatOuter
import CORALean.HybridDynamics.Theorems.LocationReachFloatOuter

/-!
# `HybridAutomaton.reachFloat` holds every run it was asked about

Every run from `X₀` at `ℓ` with `k ≤ K` jumps and a duration of at most
`tFinal` ends in one of the computed sets, paired with the location it ends at.
By induction on the run, one case per constructor as `RunOuter`'s: a stay is
held by `Location.Trajectory.reachFloat_outer`, its duration being at most the
whole budget; a jump leaves the stay in one of its time-interval sets, in the
invariant and in the guard, so `Location.guardIntersectFloat_outer` and
`Transition.jumpFloat_outer` put the reset state in the set the recursive call
starts from, with one jump and less time left.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A successful `mapM` in `Option` has an answer for every entry. -/
theorem aux_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | a :: l, l', h, a', ha' => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨c, hc, hfc⟩ := aux_mapM_some hbs a' ha'
      exact ⟨c, List.mem_cons_of_mem _ hc, hfc⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run (`run_iff_exists_runUntil`: a `Run` with a duration) from `X₀` at `ℓ`, with at
most `K` jumps and lasting at most `tFinal`, ends in a computed set of its final location;
at `reachSet` this is `reachSet_subset_reachFloat`. -/
theorem HybridAutomaton.reachFloat_outer
    (HA : HybridAutomaton (Zonotope 𝕋) (HPolytope 𝕋) L 𝕋 n) {tFinal : ℚ}
    {options : LinearSys.ReachOptions 𝕋} {T : ℝ} {k : ℕ} {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.RunUntil T k ℓ x ℓ' y) (hT : T ≤ tFinal) {K : ℕ} (hk : k ≤ K)
    {X₀ : Zonotope 𝕋 n} (hx : x ∈ construct X₀) {out : List (L × Zonotope 𝕋 n)}
    (h : HA.reachFloat tFinal options K ℓ X₀ = some out) :
    ∃ p ∈ out, p.1 = ℓ' ∧ y ∈ construct p.2 := by -- --- PROOF ---
  induction run generalizing K X₀ out with
  | @flow T ℓ τ x u traj hτ =>
    -- the stay itself, held by one of the location's sets whatever `K` is
    unfold HybridAutomaton.reachFloat at h
    obtain ⟨Rs, hRs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨R, hR, hy⟩ := traj.reachFloat_outer hRs hx (hτ.trans hT)
      ⟨traj.nonneg, le_rfl⟩
    have hhere : (ℓ, R) ∈ Rs.map fun R => (ℓ, R) := List.mem_map.mpr ⟨R, hR, rfl⟩
    cases K with
    | zero =>
      cases h
      exact ⟨_, hhere, rfl, hy⟩
    | succ K =>
      obtain ⟨next, -, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact ⟨_, List.mem_append_left _ hhere, rfl, hy⟩
  | @jump T k ℓ ℓ' τ x u y e traj hτ hmem hguard rest ih =>
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    unfold HybridAutomaton.reachFloat at h
    obtain ⟨Rs, hRs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨next, hnext, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    -- the state at the jump is in a set of the stay, in the invariant and in the guard
    obtain ⟨R, hR, hxτ⟩ := traj.reachFloat_outer hRs hx (hτ.trans hT)
      ⟨traj.nonneg, le_rfl⟩
    obtain ⟨Rg, hRg, hxRg⟩ := (HA.loc ℓ).guardIntersectFloat_outer e.guard hR hxτ
      (traj.invariant τ ⟨traj.nonneg, le_rfl⟩) hguard
    -- so the reset state is in the set the transition's branch continues from
    have hreset : e.reset (x τ) ∈ construct (e.jumpFloat Rg.zonotope) :=
      e.jumpFloat_outer Set.inter_subset_left (Interval.zonotope_contains Rg hxRg) hguard
    obtain ⟨o, ho, hfo⟩ := aux_mapM_some hnext e hmem
    simp only [hRg] at hfo
    obtain ⟨p, hp, hpℓ, hpy⟩ := ih (by linarith [traj.nonneg])
      (Nat.le_of_succ_le_succ hk) hreset hfo
    exact ⟨p, List.mem_append_right _ (List.mem_flatten_of_mem ho hp), hpℓ, hpy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
