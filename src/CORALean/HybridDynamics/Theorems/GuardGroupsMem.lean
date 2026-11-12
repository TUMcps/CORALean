module

public import CORALean.HybridDynamics.Theorems.GuardGroupsChain

@[expose] public section

/-!
# Every hit lies in a group of `Location.guardGroups`

A hit `(g, k)` is in the group of guard `g` whose run of set indices holds `k`, and the first index
of that run is at most `k`: the groups run one by one (`Location.guardGroups_chain`), upward.

## Inputs
* `hits` – hits `(transition, set index)`
* `g` – transition
* `k` – set index

## Hypotheses
* `h` – `(g, k)` is a hit

## Conclusion
* a group of `g` starts at an index at most `k` and holds `k`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every index of the list is in a run. -/
private theorem aux_mem_gapRuns : ∀ (is : List ℕ) {k : ℕ}, k ∈ is →
    ∃ r ∈ Location.gapRuns is, k ∈ r
  | [], _, h => absurd h (List.not_mem_nil)
  | i :: is', k, h => by
    unfold Location.gapRuns
    rcases List.mem_cons.mp h with rfl | hk
    · rcases h' : Location.gapRuns is' with _ | ⟨_ | ⟨j, js⟩, rest⟩
      · simp
      · simp
      · by_cases hj : j = k + 1 <;> simp [hj]
    · obtain ⟨r, hr, hkr⟩ := aux_mem_gapRuns is' hk
      rcases h' : Location.gapRuns is' with _ | ⟨_ | ⟨j, js⟩, rest⟩
      · simp [h'] at hr
      · rw [h'] at hr
        rcases List.mem_cons.mp hr with rfl | hr
        · simp at hkr
        · exact ⟨r, by simp [hr], hkr⟩
      · rw [h'] at hr
        by_cases hji : j = i + 1
        · subst hji
          simp only [if_true]
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨i :: (i + 1) :: js, List.mem_cons_self, List.mem_cons_of_mem _ hkr⟩
          · exact ⟨r, by simp [hr], hkr⟩
        · simp only [hji, if_false]
          exact ⟨r, by simpa using Or.inr hr, hkr⟩

/-- The first entry of a run that goes up by one is its least. -/
private theorem aux_head_le {a : ℕ} {l : List ℕ}
    (h : List.IsChain (fun a b => b = a + 1) (a :: l)) {k : ℕ} (hk : k ∈ a :: l) : -- --- CONCL ---
    a ≤ k := by -- --- PROOF ---
  induction l generalizing a with
  | nil => simp at hk; omega
  | cons b l ih =>
    have hab : b = a + 1 := (List.isChain_cons_cons.mp h).1
    have hbl := (List.isChain_cons_cons.mp h).2
    rcases List.mem_cons.mp hk with rfl | hk
    · exact le_rfl
    · have := ih hbl hk
      omega

/-- What a fold of `f g ++ acc` holds is `acc` or some `f g`, and conversely. -/
private theorem aux_mem_foldl_iff {X : Type} (gs : List ℕ) (f : ℕ → List X) (acc : List X)
    (x : X) : -- --- CONCL ---
    x ∈ gs.foldl (fun acc g => f g ++ acc) acc ↔ x ∈ acc ∨ ∃ g ∈ gs, x ∈ f g := by -- --- PROOF ---
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨g', hg', h⟩)
      · exact Or.inr ⟨g, Or.inl rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨g', Or.inr hg', h⟩
    · rintro (h | ⟨g', hg' | hg', h⟩)
      · exact Or.inl (Or.inr h)
      · subst hg'; exact Or.inl (Or.inl h)
      · exact Or.inr ⟨g', hg', h⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- A hit is in a group of its guard, whose first index is at most the hit's. -/
theorem Location.guardGroups_mem (hits : List (ℕ × ℕ)) {g k : ℕ}
    (h : (g, k) ∈ hits) : -- --- CONCL ---
    ∃ j₀ js, (g, j₀ :: js) ∈ Location.guardGroups hits ∧ j₀ ≤ k ∧
      k ∈ j₀ :: js := by -- --- PROOF ---
  -- the run of `g` that holds `k`
  have hk : k ∈ (hits.filter fun h => h.1 = g).map Prod.snd :=
    List.mem_map.mpr ⟨(g, k), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩
  obtain ⟨r, hr, hkr⟩ := aux_mem_gapRuns _ hk
  have hg : g ∈ ((hits.map Prod.fst).dedup).mergeSort := by
    simpa using ⟨k, h⟩
  obtain ⟨j₀, js, rfl⟩ : ∃ j₀ js, r = j₀ :: js := by
    cases r with
    | nil => simp at hkr
    | cons a l => exact ⟨a, l, rfl⟩
  have hmem : (g, j₀ :: js) ∈ Location.guardGroups hits := by
    unfold Location.guardGroups
    dsimp only
    -- the run is the last one of its guard, or one of the others
    have hne : Location.gapRuns ((hits.filter fun h => h.1 = g).map Prod.snd) ≠ [] :=
      List.ne_nil_of_mem hr
    have hsplit := List.dropLast_append_getLast hne
    rw [← hsplit] at hr
    rcases List.mem_append.mp hr with hd | hl
    · refine List.mem_append_left _ ((aux_mem_foldl_iff _ _ _ _).mpr (Or.inr ⟨g, hg, ?_⟩))
      exact List.mem_map.mpr ⟨_, List.mem_reverse.mpr hd, rfl⟩
    · refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨g, hg, ?_⟩)
      have : (j₀ :: js) =
          (Location.gapRuns ((hits.filter fun h => h.1 = g).map Prod.snd)).getLast hne := by
        simpa using hl
      rw [List.getLast?_eq_getLast_of_ne_nil hne, this]
      rfl
  refine ⟨j₀, js, hmem, ?_, hkr⟩
  exact aux_head_le (Location.guardGroups_chain hits _ hmem) hkr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
