module

public import CORALean.HybridDynamics.Operations.GuardGroups

@[expose] public section

/-!
# The groups of `Location.guardGroups` have no gaps

Within a group the set indices run one by one, each the successor of the one before: a group is
a single crossing of its guard.

## Inputs
* `hits` – hits `(transition, set index)`

## Hypotheses
* none

## Conclusion
* every group's indices run one by one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each run of `gapRuns` runs one by one. -/
private theorem aux_chain_gapRuns (is : List ℕ) : -- --- CONCL ---
    ∀ r ∈ Location.gapRuns is, List.IsChain (fun a b => b = a + 1) r := by -- --- PROOF ---
  -- by induction on the indices
  induction is with
  | nil => simp [Location.gapRuns]
  | cons i is ih =>
    unfold Location.gapRuns
    -- the runs of the tail, by the shape of the first one
    rcases h : Location.gapRuns is with _ | ⟨_ | ⟨j, js⟩, rest⟩
    · simp
    -- (an empty first run, which does not occur)
    · simp only [h] at ih
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp
      · exact ih r (List.mem_cons_of_mem _ hr)
    · simp only [h] at ih
      by_cases hj : j = i + 1
      · simp only [hj, if_true]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · have := ih (j :: js) List.mem_cons_self
          subst hj
          exact List.IsChain.cons_cons rfl this
        · exact ih r (List.mem_cons_of_mem _ hr)
      · simp only [hj, if_false]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        · exact ih r hr

/-- What holds of everything a fold adds and of its start holds of its result. -/
private theorem aux_foldl_prop {X : Type} (P : X → Prop) (gs : List ℕ) (f : ℕ → List X)
    (hf : ∀ g, ∀ x ∈ f g, P x) (acc : List X) (hacc : ∀ x ∈ acc, P x) : -- --- CONCL ---
    ∀ x ∈ gs.foldl (fun acc g => f g ++ acc) acc, P x := by -- --- PROOF ---
  induction gs generalizing acc with
  | nil => simpa using hacc
  | cons g gs ih =>
    rw [List.foldl_cons]
    refine ih _ fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · exact hf g x hx
    · exact hacc x hx


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set indices of a group run one by one: no gap is left. -/
theorem Location.guardGroups_chain (hits : List (ℕ × ℕ)) : -- --- CONCL ---
    ∀ grp ∈ Location.guardGroups hits,
      List.IsChain (fun a b => b = a + 1) grp.2 := by -- --- PROOF ---
  intro grp hgrp
  unfold Location.guardGroups at hgrp
  dsimp only at hgrp
  rcases List.mem_append.mp hgrp with hf | hl
  -- a group that went to the front
  · refine aux_foldl_prop (fun x : ℕ × List ℕ => List.IsChain (fun a b => b = a + 1) x.2) _ _
      (fun g x hx => ?_) [] (by simp) grp hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact aux_chain_gapRuns _ r (List.dropLast_subset _ (List.mem_reverse.mp hr))
  -- a group that stayed behind
  · obtain ⟨g, _, hg⟩ := List.mem_filterMap.mp hl
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hg
    exact aux_chain_gapRuns _ r (List.mem_of_getLast? hr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
