module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GreedyTarget

@[expose] public section

/-!
# `greedy(G)` keeps the lightest outgoing edge

`[1, Thm. 2]`: `greedy(G)` of `[1, Alg. 2]`, line 2, keeps only the outgoing edge with the smallest
edge weight for each node. `greedyTarget` returns no edge exactly at a node that has none, and
otherwise an edge of `G` no outgoing edge of the node undercuts.

## Inputs
* `G` – relation of admissible pairs
* `w` – pair weights
* `i` – generator index

## Hypotheses
* none

## Conclusion
* none exactly if no partner is admissible, else the lightest one

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold's invariant: what the best edge so far is among the targets seen. -/
private def aux_GreedyInv (G : Fin h → Fin h → Prop) (w : Fin h → Fin h → ℕ) (i : Fin h)
    (done : List (Fin h)) (best : Option (Fin h)) : Prop :=
  (∀ b, best = some b → b ∈ done ∧ G i b ∧ ∀ j ∈ done, G i j → w i b ≤ w i j) ∧
    (best = none → ∀ j ∈ done, ¬ G i j)

/-- One target considered: it replaces the best if it is an edge and lighter. -/
private def aux_greedyStep (G : Fin h → Fin h → Prop) [DecidableRel G] (w : Fin h → Fin h → ℕ)
    (i : Fin h) (best : Option (Fin h)) (j : Fin h) : Option (Fin h) :=
  if G i j then
    match best with
    | none => some j
    | some b => if w i j < w i b then some j else some b
  else best

/-- One more target either leaves the best alone or replaces it. -/
private theorem aux_greedy_step (G : Fin h → Fin h → Prop) [DecidableRel G] (w : Fin h → Fin h → ℕ)
    (i : Fin h) (done : List (Fin h)) (best : Option (Fin h)) (j : Fin h)
    (hinv : aux_GreedyInv G w i done best) : -- --- CONCL ---
    aux_GreedyInv G w i (done ++ [j]) (aux_greedyStep G w i best j) := by -- --- PROOF ---
  obtain ⟨hs, hn⟩ := hinv
  unfold aux_greedyStep
  -- an edge to `j` competes with the best so far; a non-edge changes nothing
  by_cases hG : G i j
  · rw [if_pos hG]
    rcases best with _ | b
    · refine ⟨fun b' hb' => ?_, fun hc => by simp at hc⟩
      obtain rfl : j = b' := Option.some.inj hb'
      refine ⟨by simp, hG, ?_⟩
      intro j' hj' hGj'
      rcases List.mem_append.mp hj' with hj' | hj'
      · exact absurd hGj' (hn rfl j' hj')
      · rw [List.mem_singleton.mp hj']
    · obtain ⟨hb, hGb, hmin⟩ := hs b rfl
      -- the lighter of `j` and the old best stays
      by_cases hlt : w i j < w i b
      · simp only [hlt, if_true]
        refine ⟨fun b' hb' => ?_, fun hc => by simp at hc⟩
        obtain rfl : j = b' := Option.some.inj hb'
        refine ⟨by simp, hG, ?_⟩
        intro j' hj' hGj'
        rcases List.mem_append.mp hj' with hj' | hj'
        · exact le_trans hlt.le (hmin j' hj' hGj')
        · rw [List.mem_singleton.mp hj']
      · -- the old best stays
        simp only [hlt, if_false]
        refine ⟨fun b' hb' => ?_, fun hc => by simp at hc⟩
        obtain rfl : b = b' := Option.some.inj hb'
        refine ⟨List.mem_append_left _ hb, hGb, ?_⟩
        intro j' hj' hGj'
        rcases List.mem_append.mp hj' with hj' | hj'
        · exact hmin j' hj' hGj'
        · rw [List.mem_singleton.mp hj']; omega
  · rw [if_neg hG]
    refine ⟨fun b hb => ?_, fun hc => ?_⟩
    · obtain ⟨hb', hGb, hmin⟩ := hs b hb
      refine ⟨List.mem_append_left _ hb', hGb, fun j' hj' hGj' => ?_⟩
      rcases List.mem_append.mp hj' with hj' | hj'
      · exact hmin j' hj' hGj'
      · rw [List.mem_singleton.mp hj'] at hGj'; exact absurd hGj' hG
    · intro j' hj'
      rcases List.mem_append.mp hj' with hj' | hj'
      · exact hn hc j' hj'
      · rw [List.mem_singleton.mp hj']; exact hG

/-- The invariant survives the whole fold. -/
private theorem aux_greedy_fold (G : Fin h → Fin h → Prop) [DecidableRel G] (w : Fin h → Fin h → ℕ)
    (i : Fin h) (l done : List (Fin h)) (best : Option (Fin h))
    (hinv : aux_GreedyInv G w i done best) : -- --- CONCL ---
    aux_GreedyInv G w i (done ++ l) (l.foldl (aux_greedyStep G w i) best) := by -- --- PROOF ---
  induction l generalizing done best with
  | nil => simpa using hinv
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [show done ++ j :: l = (done ++ [j]) ++ l by simp]
    exact ih (done ++ [j]) _ (aux_greedy_step G w i done best j hinv)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `greedyTarget` is `none` exactly at a node without outgoing edges, and otherwise
an outgoing edge of smallest weight. -/
theorem PolyZonotope.greedyTarget_spec (G : Fin h → Fin h → Prop) [DecidableRel G]
    (w : Fin h → Fin h → ℕ) (i : Fin h) : -- --- CONCL ---
    (PolyZonotope.greedyTarget G w i = none ↔ ∀ j, ¬ G i j) ∧
      ∀ j, PolyZonotope.greedyTarget G w i = some j →
        G i j ∧ ∀ j', G i j' → w i j ≤ w i j' := by -- --- PROOF ---
  have hfin := aux_greedy_fold G w i (List.finRange h) [] none ⟨by simp, by simp⟩
  have hmem : ∀ j : Fin h, j ∈ [] ++ List.finRange h := fun j => by simp
  refine ⟨⟨fun hc j hj => ?_, fun hall => ?_⟩, fun j hj => ?_⟩
  · exact hfin.2 hc j (hmem j) hj
  · rcases hr : PolyZonotope.greedyTarget G w i with _ | b
    · rfl
    · exact absurd (hfin.1 b hr).2.1 (hall b)
  · obtain ⟨-, hGj, hmin⟩ := hfin.1 j hj
    exact ⟨hGj, fun j' hj' => hmin j' (hmem j') hj'⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
