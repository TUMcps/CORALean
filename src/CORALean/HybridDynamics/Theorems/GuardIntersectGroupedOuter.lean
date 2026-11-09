module

public import CORALean.HybridDynamics.Operations.GuardIntersectGrouped

@[expose] public section

/-!
# `Location.guardIntersectGrouped` holds every state that meets the guard

A state of a reach set that is hit and lies in the guard of the hit transition lies in the
enclosure of its crossing, whenever the method encloses the states of the sets it is given that
lie in the guard. Grouping and gap splitting lose no hit: a hit `(g, j)` is in a group `(g, r)`
with `j ∈ r`.

## Inputs
* `enclose` – the method
* `sets` – reach sets
* `hits` – hits `(transition, set index)`
* `memZ` – the states of a reach set
* `memE` – the states of an enclosure
* `Gd` – the guard of a transition
* `g` – transition
* `j` – set index
* `Z` – reach set
* `x` – state

## Hypotheses
* `hsound` – the method encloses the states of its sets that lie in the guard
* `hj` – the hit `(g, j)` is among the hits
* `hZ` – the set `j` is `Z`
* `hx` – the state lies in `Z`
* `hg` – the state lies in the guard of `g`

## Conclusion
* a crossing of the transition `g` has an enclosure holding the state
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {Z E X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The runs hold exactly the indices, in order. -/
private theorem aux_flatten_gapRuns (is : List ℕ) : -- --- CONCL ---
    (Location.gapRuns is).flatten = is := by -- --- PROOF ---
  induction is with
  | nil => rfl
  | cons i is ih =>
    unfold Location.gapRuns
    -- by the shape of the first run of the tail
    rcases h : Location.gapRuns is with _ | ⟨_ | ⟨j, js⟩, rest⟩
    · simp [h] at ih; simp [← ih]
    · simp [h] at ih ⊢; simp [← ih]
    · by_cases hj : j = i + 1
      · simp [hj, h] at ih ⊢; simp [← ih]
      · simp [hj, h] at ih ⊢; simp [← ih]

/-- A run is among the first ones or the last. -/
private theorem aux_mem_dropLast_or_last {α : Type} {r : α} {l : List α}
    (h : r ∈ l) : -- --- CONCL ---
    r ∈ l.dropLast ∨ l.getLast? = some r := by -- --- PROOF ---
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · simp at h
  · simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      List.mem_append, List.mem_singleton] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h])

/-- The groups folded in stay in the result. -/
private theorem aux_mem_foldl {X : Type} (gs : List ℕ) (f : ℕ → List X) (acc : List X) (x : X)
    (h : x ∈ acc ∨ ∃ g ∈ gs, x ∈ f g) : -- --- CONCL ---
    x ∈ gs.foldl (fun acc g => f g ++ acc) acc := by -- --- PROOF ---
  induction gs generalizing acc with
  | nil => simpa using h
  | cons g gs ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    rcases h with h | ⟨g', hg', hx⟩
    · exact Or.inl (List.mem_append_right _ h)
    · rcases List.mem_cons.mp hg' with rfl | hg'
      · exact Or.inl (List.mem_append_left _ hx)
      · exact Or.inr ⟨g', hg', hx⟩

/-- A hit of the guard `g` at the set `j` is in a group of `g`. -/
private theorem aux_guardGroups_cover (hits : List (ℕ × ℕ)) {g j : ℕ}
    (hj : (g, j) ∈ hits) : -- --- CONCL ---
    ∃ grp ∈ Location.guardGroups hits, grp.1 = g ∧ j ∈ grp.2 := by -- --- PROOF ---
  have hg : g ∈ ((hits.map Prod.fst).dedup).mergeSort := by
    simpa using List.mem_map_of_mem (f := Prod.fst) hj
  -- `j` is in one of the runs of the indices of `g`
  have hjs : j ∈ (hits.filter fun h => h.1 = g).map Prod.snd :=
    List.mem_map.mpr ⟨(g, j), List.mem_filter.mpr ⟨hj, by simp⟩, rfl⟩
  rw [← aux_flatten_gapRuns ((hits.filter fun h => h.1 = g).map Prod.snd)] at hjs
  obtain ⟨r, hr, hjr⟩ := List.mem_flatten.mp hjs
  unfold Location.guardGroups
  dsimp only
  -- the run went to the front, or it stayed
  rcases aux_mem_dropLast_or_last hr with hd | hl
  · refine ⟨(g, r), List.mem_append_left _ ?_, rfl, hjr⟩
    refine aux_mem_foldl _ (fun g => ((Location.gapRuns ((hits.filter fun h => h.1 = g).map
      Prod.snd)).dropLast.reverse.map fun r => (g, r))) [] (g, r)
      (Or.inr ⟨g, hg, ?_⟩)
    exact List.mem_map.mpr ⟨r, List.mem_reverse.mpr hd, rfl⟩
  · refine ⟨(g, r), List.mem_append_right _ (List.mem_filterMap.mpr ⟨g, hg, ?_⟩), rfl, hjr⟩
    simp [hl]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.guardIntersectGrouped_outer (enclose : ℕ → List Z → Option E) (sets : List Z)
    (hits : List (ℕ × ℕ)) (memZ : Z → Set X) (memE : E → Set X) (Gd : ℕ → Set X)
    (hsound : ∀ g (P : List Z) (Z : Z), Z ∈ P → ∀ x ∈ memZ Z, x ∈ Gd g →
      ∃ R, enclose g P = some R ∧ x ∈ memE R)
    {g j : ℕ} (hj : (g, j) ∈ hits) {Z : Z} (hZ : sets[j]? = some Z)
    {x : X} (hx : x ∈ memZ Z) (hg : x ∈ Gd g) : -- --- CONCL ---
    ∃ e ∈ Location.guardIntersectGrouped enclose sets hits,
      e.1 = g ∧ x ∈ memE e.2.2.2 := by -- --- PROOF ---
  -- the crossing of `g` that holds `j`
  obtain ⟨grp, hgrp, rfl, hjr⟩ := aux_guardGroups_cover hits hj
  -- the method encloses its sets, `Z` among them
  have hZP : Z ∈ grp.2.filterMap fun j => sets[j]? :=
    List.mem_filterMap.mpr ⟨j, hjr, hZ⟩
  obtain ⟨R, hR, hxR⟩ := hsound grp.1 _ Z hZP x hx hg
  -- so the crossing is kept
  unfold Location.guardIntersectGrouped
  obtain ⟨g, r⟩ := grp
  cases r with
  | nil => simp at hjr
  | cons j₀ js =>
    refine ⟨(g, j₀, (j₀ :: js).getLast (List.cons_ne_nil _ _), R),
      List.mem_filterMap.mpr ⟨(g, j₀ :: js), hgrp, ?_⟩, rfl, hxR⟩
    simp only [hR]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
