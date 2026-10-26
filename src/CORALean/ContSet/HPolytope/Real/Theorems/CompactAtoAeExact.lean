module

public import CORALean.ContSet.HPolytope.Real.Operations.CompactAtoAe
public import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct
public import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact

@[expose] public section

/-!
# `compactAtoAe` denotes the same set, exactly

A pair `aᵀx ≤ b`, `-aᵀx ≤ -b` is the equality `aᵀx = b`, and the equalities appended by the loop
imply the rows that were moved.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* `compactAtoAe` denotes the same set, exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The set of `aux_moveToEq`. -/
private theorem HPolytope.aux_moveToEq_construct (P : HPolytope α) (S : Finset (Fin P.m))
    (L : List (Fin P.m)) : -- --- CONCL ---
    (P.aux_moveToEq S L).construct
      = {x | (∀ i ∈ S, P.A i x ≤ P.b i) ∧ (∀ r, P.Ae r x = P.be r) ∧
          ∀ i ∈ L, P.A i x = P.b i} := by -- --- PROOF ---
  ext x
  simp only [HPolytope.construct, HPolytope.aux_moveToEq, Set.mem_setOf_eq]
  -- the kept inequalities, indexed by `S` rather than by `Fin S.card`
  have h1 : (∀ k : Fin S.card, P.A (S.equivFin.symm k).1 x ≤ P.b (S.equivFin.symm k).1)
      ↔ ∀ i ∈ S, P.A i x ≤ P.b i := by
    constructor
    · intro h i hi
      simpa using h (S.equivFin ⟨i, hi⟩)
    · intro h k
      exact h _ (S.equivFin.symm k).2
  have h2 : (∀ k : Fin (P.me + L.length), (Fin.append P.Ae fun k => P.A (L.get k)) k x
        = (Fin.append P.be fun k => P.b (L.get k)) k)
      ↔ (∀ r, P.Ae r x = P.be r) ∧ ∀ i ∈ L, P.A i x = P.b i := by
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right]
    refine and_congr Iff.rfl ⟨fun h i hi => ?_, fun h k => h _ (List.get_mem L k)⟩
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hi
    exact h k
  rw [h1, h2]

end


section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- What the loop of `compact_(P, 'AtoAe')` guarantees. -/
private theorem HPolytope.aux_atoAeState_spec (Q : HPolytope α) : -- --- CONCL ---
    (∀ k ∈ Q.aux_atoAeState.2, ∃ j, Q.A j = -Q.A k ∧ Q.b j = -Q.b k) ∧
    ∀ i ∈ Q.aux_atoAeState.1, ∃ k ∈ Q.aux_atoAeState.2,
      i = k ∨ (Q.A i = -Q.A k ∧ Q.b i = -Q.b k) := by -- --- PROOF ---
  unfold HPolytope.aux_atoAeState
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

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactAtoAe_exact (P : HPolytope (Vec ℝ n)) : -- --- CONCL ---
    P.compactAtoAe.construct = P.construct := by -- --- PROOF ---
  rw [← P.normalizeRows_exact]
  unfold HPolytope.compactAtoAe
  generalize P.normalizeRows = Q
  obtain ⟨hadd, hmov⟩ := Q.aux_atoAeState_spec
  simp only [HPolytope.aux_moveToEq_construct, Finset.mem_filter, Finset.mem_univ, true_and]
  ext x
  simp only [Set.mem_setOf_eq, HPolytope.construct]
  constructor
  · -- the moved rows are implied by the appended equalities
    rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, h2⟩
    by_cases hi : i ∈ Q.aux_atoAeState.1
    · obtain ⟨k, hk, hik⟩ := hmov i hi
      have hkx := h3 k hk
      rcases hik with rfl | ⟨hA, hb⟩
      · exact hkx.le
      · rw [hA, hb]
        simp [hkx]
    · exact h1 i hi
  · -- an appended equality is the pair of inequalities
    rintro ⟨h1, h2⟩
    refine ⟨fun i _ => h1 i, h2, fun k hk => ?_⟩
    obtain ⟨j, hA, hb⟩ := hadd k hk
    have h1k := h1 k
    have h1j := h1 j
    rw [hA, hb] at h1j
    simp only [LinearMap.neg_apply] at h1j
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
