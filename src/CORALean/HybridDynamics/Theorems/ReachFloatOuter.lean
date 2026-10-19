module

public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.HybridDynamics.Definitions.IsRunUntil
public import CORALean.HybridDynamics.Operations.ReachFloat
public import CORALean.HybridDynamics.Theorems.GuardIntersectFloatOuter
public import CORALean.HybridDynamics.Theorems.JumpFloatOuter
public import CORALean.HybridDynamics.Theorems.LocationReachFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `HybridAutomaton.reachFloat` holds every run it was asked about

Every run from `X₀` at `ℓ` with `k ≤ K` jumps and a duration of at most
`tFinal` ends in one of the computed sets, paired with the location it ends at.
By induction on the run, one case per constructor as `RunOuter`'s: a stay is
held by `Location.IsTrajectory.reachFloat_outer`, its duration being at most the
whole budget; a jump leaves the stay in one of its time-interval sets, in the
invariant and in the guard, so `Location.guardIntersectFloat_outer` and
`Transition.jumpFloat_outer` put the reset state in the set the recursive call
starts from, with one jump and less time left.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A successful `mapM` in `Option` has an answer for every entry. -/
theorem aux_mapM_some {α β : Type} {f : α → Option β} : -- --- STMT ---
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

/-- Every run (`isRun_iff_exists_isRunUntil`: a `IsRun` with a duration) from `X₀` at `ℓ`, with at
most `K` jumps and lasting at most `tFinal`, ends in a computed set of its final location;
at `reachSetExact` this is `reachSetExact_subset_reachFloat`. -/
theorem HybridAutomaton.reachFloat_outer
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋
    n) {tFinal : ℚ} {options : LinearSys.ReachOptions 𝕋} {T : ℝ} {k : ℕ} {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.IsRunUntil T k ℓ x ℓ' y) (hT : T ≤ tFinal) {K : ℕ} (hk : k ≤ K)
    {X₀ : Zonotope (Vec 𝕋 n)} (hx : x ∈ construct X₀) : -- --- STMT ---
    ∀ out ∈ HA.reachFloat tFinal options K ℓ X₀,
      ∃ p ∈ out, p.1 = ℓ' ∧ y ∈ construct p.2 := by -- --- PROOF ---
  intro out (h : HA.reachFloat tFinal options K ℓ X₀ = some out)
  induction run generalizing K X₀ out with
  | @flow T ℓ τ x u w traj hτ =>
    -- the stay itself, held by one of the location's sets whatever `K` is
    unfold HybridAutomaton.reachFloat at h
    obtain ⟨Rs, hRs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨R, hR, hy⟩ := traj.reachFloat_outer hx (hτ.trans hT)
      ⟨traj.nonneg, le_rfl⟩ _ hRs
    have hhere : (ℓ, R) ∈ Rs.map fun R => (ℓ, R) := List.mem_map.mpr ⟨R, hR, rfl⟩
    cases K with
    | zero =>
      cases h
      exact ⟨_, hhere, rfl, hy⟩
    | succ K =>
      obtain ⟨next, -, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact ⟨_, List.mem_append_left _ hhere, rfl, hy⟩
  | @jump T k ℓ ℓ' τ x u w y e traj hτ hmem hguard rest ih =>
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    unfold HybridAutomaton.reachFloat at h
    obtain ⟨Rs, hRs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨next, hnext, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    -- the state at the jump is in a set of the stay, in the invariant and in the guard
    obtain ⟨R, hR, hxτ⟩ := traj.reachFloat_outer hx (hτ.trans hT)
      ⟨traj.nonneg, le_rfl⟩ _ hRs
    obtain ⟨Rg, hRg, hxRg⟩ := (HA.loc ℓ).guardIntersectFloat_outer e.guard hR hxτ
      (traj.invariant τ ⟨traj.nonneg, le_rfl⟩) hguard
    -- so the reset state is in the set the transition's branch continues from
    have hreset : e.reset (x τ) ∈ construct (e.jumpFloat Rg.zonotope) :=
      e.jumpFloat_outer Set.inter_subset_left (Interval.zonotope_contains Rg hxRg) hguard
    obtain ⟨o, ho, hfo⟩ := aux_mapM_some hnext e hmem
    simp only [hRg] at hfo
    obtain ⟨p, hp, hpℓ, hpy⟩ := ih (by linarith [traj.nonneg])
      (Nat.le_of_succ_le_succ hk) hreset _ hfo
    exact ⟨p, List.mem_append_right _ (List.mem_flatten_of_mem ho hp), hpℓ, hpy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
