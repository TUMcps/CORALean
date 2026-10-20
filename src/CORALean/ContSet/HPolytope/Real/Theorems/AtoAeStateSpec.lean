module

public import CORALean.ContSet.HPolytope.Real.Operations.AtoAeState

@[expose] public section

/-!
# What the loop of `compact_(P, 'AtoAe')` guarantees

Every row it appends as an equality has an inverted partner among the inequality rows, and
every row it marks as moved is an appended row or the inverted partner of one: so each moved
row is implied by an appended equality, and each appended equality by two inequalities.

## Inputs
* `Q` – H-polytope

## Hypotheses
* none

## Conclusion
* every moved row has an inverted partner, and every matched row is moved or inverted to a moved one
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.atoAeState_spec (Q : HPolytope α) : -- --- CONCL ---
    (∀ k ∈ Q.atoAeState.2, ∃ j, Q.A j = -Q.A k ∧ Q.b j = -Q.b k) ∧
    ∀ i ∈ Q.atoAeState.1, ∃ k ∈ Q.atoAeState.2,
      i = k ∨ (Q.A i = -Q.A k ∧ Q.b i = -Q.b k) := by -- --- PROOF ---
  unfold HPolytope.atoAeState
  -- the invariant, along the loop
  suffices h : ∀ (l : List (Fin Q.m)) (st : Finset (Fin Q.m) × List (Fin Q.m)),
      ((∀ k ∈ st.2, ∃ j, Q.A j = -Q.A k ∧ Q.b j = -Q.b k) ∧
        ∀ i ∈ st.1, ∃ k ∈ st.2, i = k ∨ (Q.A i = -Q.A k ∧ Q.b i = -Q.b k)) →
      let r := l.foldl (fun st i =>
        if i ∈ st.1 then st
        else
          let idxInverted := Finset.univ.filter fun j => Q.A j = -Q.A i ∧ Q.b j = -Q.b i
          if idxInverted.Nonempty then (st.1 ∪ idxInverted ∪ {i}, st.2 ++ [i]) else st) st
      (∀ k ∈ r.2, ∃ j, Q.A j = -Q.A k ∧ Q.b j = -Q.b k) ∧
        ∀ i ∈ r.1, ∃ k ∈ r.2, i = k ∨ (Q.A i = -Q.A k ∧ Q.b i = -Q.b k) from
    h _ _ ⟨by simp, by simp⟩
  intro l
  -- one step of the loop keeps the invariant
  induction l with
  | nil => intro st hst; exact hst
  | cons a l ih =>
    intro st hst
    simp only [List.foldl_cons]
    apply ih
    by_cases ha : a ∈ st.1
    · simpa [ha] using hst
    · -- an unmatched row: look for its inverted partners
      simp only [ha, if_false]
      by_cases hne : (Finset.univ.filter fun j => Q.A j = -Q.A a ∧ Q.b j = -Q.b a).Nonempty
      · -- there is one: the row is appended, with its partners moved
        simp only [hne, if_true]
        obtain ⟨j₀, hj₀⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀
        refine ⟨fun k hk => ?_, fun i hi => ?_⟩
        · -- an appended row has a partner
          rcases List.mem_append.mp hk with hk | hk
          · exact hst.1 k hk
          · rw [List.mem_singleton.mp hk]; exact ⟨j₀, hj₀⟩
        · -- a moved row is an old one, a partner of `a`, or `a`
          rcases Finset.mem_union.mp hi with hi | hi
          · rcases Finset.mem_union.mp hi with hi | hi
            · obtain ⟨k, hk, hik⟩ := hst.2 i hi
              exact ⟨k, List.mem_append_left _ hk, hik⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
              exact ⟨a, List.mem_append_right _ (List.mem_singleton_self a), Or.inr hi⟩
          · exact ⟨a, List.mem_append_right _ (List.mem_singleton_self a),
              Or.inl (Finset.mem_singleton.mp hi)⟩
      · simpa [hne] using hst

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
