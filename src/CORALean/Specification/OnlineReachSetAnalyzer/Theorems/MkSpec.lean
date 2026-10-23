module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Mk
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ParseSpec

@[expose] public section

/-!
# What the constructor builds

An analyzer made from a formula has the given propagation frequency, no observation and nothing
propagated; node `j` (numbered from `0`) has index `j + 1`; every node has the `dropPropagated`
given; the first node is the root, of the type of the formula, and its first parent is `0`; and
the leaves are indices of nodes.

## Inputs
* `φ` – formula to monitor
* `f` – propagation frequency
* `dp` – drop propagated times flag

## Hypotheses
* none

## Conclusion
* the analyzer has no observations and nothing propagated
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.mk?_spec
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (f : ℕ)
    (dp : Bool) : -- --- CONCL ---
    ∀ obj ∈ OnlineReachSetAnalyzer.mk? φ f dp,
      obj.propagationFrequency = f ∧ obj.numObservations = 0 ∧
        obj.propagated = List.replicate obj.nodes.length false ∧
        (∀ (j : ℕ) (hj : j < obj.nodes.length), obj.nodes[j].idx = j + 1) ∧
        (∀ n ∈ obj.nodes, n.dropPropagated = dp) ∧
        (∃ root, obj.nodes[0]? = some root ∧ root.kind = φ.kind ∧ root.parents.head? = some 0) ∧
        (∀ l ∈ obj.leaves, 1 ≤ l ∧ l ≤ obj.nodes.length) := by -- --- PROOF ---
  intro obj (h : OnlineReachSetAnalyzer.mk? φ f dp = some obj)
  unfold OnlineReachSetAnalyzer.mk? at h
  obtain ⟨st, hparse, rfl⟩ := Option.map_eq_some_iff.mp h
  -- the parser keeps the invariant of the nodes, from the empty list
  obtain ⟨hinv, -, hroot⟩ := OnlineReachSetAnalyzer.parse_spec dp φ 0 ⟨[], []⟩ st
    ⟨fun j hj => absurd hj (by simp), fun n hn => absurd hn (by simp)⟩ hparse
  refine ⟨rfl, rfl, rfl, hinv.1, fun n hn => (hinv.2 n hn).1, hroot rfl, fun l hl => ?_⟩
  -- a leaf is the index of a node
  obtain ⟨hl, -⟩ := List.mem_filter.mp hl
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
  have := List.mem_range.mp hj
  exact ⟨Nat.succ_pos j, this⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
