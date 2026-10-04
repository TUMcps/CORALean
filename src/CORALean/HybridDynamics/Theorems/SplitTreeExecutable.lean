import CORALean.HybridDynamics.Theorems.IdentGuardEq
import CORALean.HybridDynamics.Operations.SplitTreeRegions
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Basic

/-!
# The identified automaton has no execution errors

[1, Thm. 1], as its proof sketch establishes it: the leaves' invariants cover the state space;
every boundary point of an invariant lies on one of its bounding surfaces `aᵀx = b`, and there
in the guard of a transition built by [1, Prop. 1] towards some leaf, since the reset's image
lies in some invariant; and every guard maps into its target's invariant. "Executable" is not
defined in the paper; these are the two errors it names (a state outside the target invariant
after a jump, leaving an invariant without hitting a guard) and the start. Transitions are
taken from every leaf, across every surface on its path, to every leaf, with any affine reset
per surface (`I`, `0` for switching and bouncing, (17)'s fit for jumps). Whether the flow
`ẋ = Aᵢφ(x, u)` exists for all time is not part of it: for affine templates it does.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A boundary point of a polytope is on one of its bounding hyperplanes. -/
theorem aux_eq_of_mem_frontier (cs : List (Vec ℝ n × ℝ)) {x : Vec ℝ n}
    (hx : x ∈ frontier (IdentHA.polySet cs)) : ∃ p ∈ cs, p.1 ⬝ᵥ x = p.2 := by -- --- PROOF ---
  have hcont : ∀ c : Vec ℝ n, Continuous fun y : Vec ℝ n => c ⬝ᵥ y := fun c =>
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hclosed : IsClosed (IdentHA.polySet cs) := by
    have : IdentHA.polySet cs = ⋂ p ∈ cs, {y : Vec ℝ n | p.1 ⬝ᵥ y ≤ p.2} := by
      ext y; simp [IdentHA.polySet]
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_le (hcont p.1) continuous_const
  have hxs : x ∈ IdentHA.polySet cs := hclosed.frontier_subset hx
  by_contra hne
  push Not at hne
  -- all inequalities strict: an open neighbourhood inside the polytope
  have hopen : IsOpen {y : Vec ℝ n | ∀ p ∈ cs, p.1 ⬝ᵥ y < p.2} := by
    have : {y : Vec ℝ n | ∀ p ∈ cs, p.1 ⬝ᵥ y < p.2} = ⋂ p ∈ cs, {y | p.1 ⬝ᵥ y < p.2} := by
      ext y; simp
    rw [this]
    exact (List.finite_toSet cs).isOpen_biInter fun p _ => isOpen_lt (hcont p.1) continuous_const
  have hsub : {y : Vec ℝ n | ∀ p ∈ cs, p.1 ⬝ᵥ y < p.2} ⊆ IdentHA.polySet cs :=
    fun y hy p hp => (hy p hp).le
  have hin : x ∈ interior (IdentHA.polySet cs) :=
    interior_maximal hsub hopen fun p hp => lt_of_le_of_ne (hxs p hp) (hne p hp)
  exact hx.2 hin

/-- The leaves' invariants cover the state space. -/
theorem aux_exists_region (T : IdentHA.SplitTree n) (x : Vec ℝ n) :
    ∃ cs ∈ T.regions, x ∈ IdentHA.polySet cs := by -- --- PROOF ---
  induction T with
  | leaf => exact ⟨[], List.mem_singleton_self _, fun p hp => by simp at hp⟩
  | node a b l r ihl ihr =>
    -- the split puts `x` on one side or the other
    by_cases hab : a ⬝ᵥ x ≤ b
    · obtain ⟨cs, hcs, hx⟩ := ihl
      refine ⟨(a, b) :: cs, List.mem_append_left _ (List.mem_map_of_mem hcs), fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hab
      · exact hx p hp
    · obtain ⟨cs, hcs, hx⟩ := ihr
      refine ⟨(-a, -b) :: cs, List.mem_append_right _ (List.mem_map_of_mem hcs), fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [neg_dotProduct]; linarith
      · exact hx p hp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: every state starts in an invariant, every boundary point of an invariant is in
a guard leaving it, and every guard maps into its target invariant. -/
theorem IdentHA.SplitTree.executable (T : IdentHA.SplitTree n)
    (reset : Vec ℝ n × ℝ → Mat ℝ n n × Vec ℝ n) :
    (∀ x, ∃ cs ∈ T.regions, x ∈ IdentHA.polySet cs) ∧
    (∀ cs ∈ T.regions, ∀ x ∈ frontier (IdentHA.polySet cs), ∃ p ∈ cs, ∃ cs' ∈ T.regions,
      x ∈ IdentHA.conHyperplane p.1 p.2 (IdentHA.identGuard (reset p).1 (reset p).2 cs')) ∧
    (∀ cs ∈ T.regions, ∀ p ∈ cs, ∀ cs' ∈ T.regions,
      ∀ x ∈ IdentHA.conHyperplane p.1 p.2 (IdentHA.identGuard (reset p).1 (reset p).2 cs'),
        (reset p).1 *ᵥ x + (reset p).2 ∈ IdentHA.polySet cs') := by -- --- PROOF ---
  refine ⟨aux_exists_region T, fun cs _ x hx => ?_, fun cs _ p _ cs' _ x hx => ?_⟩
  · -- the surface `x` is on, and the leaf its reset lands in
    obtain ⟨p, hp, hpx⟩ := aux_eq_of_mem_frontier cs hx
    obtain ⟨cs', hcs', hr⟩ := aux_exists_region T ((reset p).1 *ᵥ x + (reset p).2)
    refine ⟨p, hp, cs', hcs', ?_⟩
    rw [IdentHA.conHyperplane_identGuard]
    exact ⟨hpx, hr⟩
  · rw [IdentHA.conHyperplane_identGuard] at hx
    exact hx.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
