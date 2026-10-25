module

public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilUnitary
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.STLInterval.Theorems.SetOrdConnected
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# A Boolean signal is a minimal disjunction of unitary signals

Every valid Boolean signal (one of finite variability) is a disjunction of finitely many unitary
signals, one for each maximal run of `true` (the intervals `findIntervals` returns, without
repetition), and no decomposition into unitary signals has fewer members: the minimal unitary
decomposition of [1, Sec. 2.3 (decomposition)] (Fig. 1). A competitor may have any number of
unitary signals, `false` ones among them; each run needs a signal of its own, since a unitary
signal lies inside one maximal run.

## Inputs
* `s` – Boolean signal

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the signal is a minimal finite disjunction of unitary signals

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.exists_minimal_unitary_decomposition (s : PointSegmentSignal ℝ)
    (hs : s.IsValid) : -- --- CONCL ---
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → PointSegmentSignal ℝ) (J : ι → STLInterval ℝ),
      (∀ i, (u i).IsValid ∧ (u i).IsUnitary (J i) ∧ (J i).set.Nonempty) ∧
      (∀ t : ℝ, 0 ≤ t → (s.at t = true ↔ ∃ i, (u i).at t = true)) ∧
      ∀ (κ : Type) (_ : Fintype κ) (v : κ → PointSegmentSignal ℝ) (K : κ → STLInterval ℝ),
        (∀ j, (v j).IsUnitary (K j)) →
        (∀ t : ℝ, 0 ≤ t → (s.at t = true ↔ ∃ j, (v j).at t = true)) →
          Fintype.card ι ≤ Fintype.card κ := by -- --- PROOF ---
  classical
  -- the maximal runs of `true`, without the empty ones and the repeated ones
  obtain ⟨hcov, hmax⟩ := s.findIntervals_spec hs id
  set L := s.findIntervals id with hL
  let F : Finset (Set ℝ) := (L.map STLInterval.set).toFinset.filter fun S => S.Nonempty
  have hF : ∀ S ∈ F, ∃ I ∈ L, I.set = S ∧ S.Nonempty := by
    intro S hS
    simp only [F, Finset.mem_filter, List.mem_toFinset, List.mem_map] at hS
    obtain ⟨⟨I, hI, rfl⟩, hne⟩ := hS
    exact ⟨I, hI, rfl, hne⟩
  haveI : Nonempty (STLInterval ℝ) := ⟨STLInterval.empty⟩
  choose! J hJL hJS hJne using hF
  -- each member of `F` is a maximal run
  have hrun : ∀ S ∈ F, ∀ t : ℝ, 0 ≤ t → t ∈ S → s.at t = true := fun S hS t ht htS => by
    have := (hcov t ht).1 ⟨J S, hJL S hS, by rw [hJS S hS]; exact htS⟩
    simpa using this
  have hmaxS : ∀ S ∈ F, ∀ t₁ ∈ S, ∀ t₂ : ℝ, 0 ≤ t₂ →
      (∀ t : ℝ, 0 ≤ t → min t₁ t₂ ≤ t → t ≤ max t₁ t₂ → s.at t = true) → t₂ ∈ S := by
    intro S hS t₁ ht₁ t₂ ht₂ h
    rw [← hJS S hS] at ht₁ ⊢
    exact hmax (J S) (hJL S hS) t₁ ht₁ t₂ ht₂ (fun t ht h1 h2 => by simpa using h t ht h1 h2)
  have hnnS : ∀ S ∈ F, ∀ t ∈ S, 0 ≤ t := fun S hS t ht => by
    rw [← hJS S hS] at ht
    exact STLInterval.zero_le_of_mem_set (J S) t ht
  refine ⟨↥F, inferInstance, fun i => PointSegmentSignal.indicator (J i.1) true false,
    fun i => J i.1, fun i => ?_, fun t ht => ?_, fun κ _ v K hK hcov' => ?_⟩
  · -- a unitary signal on the run
    obtain ⟨hv, h⟩ := PointSegmentSignal.indicator_spec (J i.1) true false
    refine ⟨hv, fun t ht => ⟨fun hat => ?_, fun hx => (h t ht).1 hx⟩, ?_⟩
    · by_contra hx
      rw [(h t ht).2 hx] at hat
      exact absurd hat (by simp)
    · rw [hJS i.1 i.2]; exact hJne i.1 i.2
  · -- the runs cover exactly where `s` is `true`
    constructor
    · intro hst
      obtain ⟨I, hI, htI⟩ := (hcov t ht).2 (by simpa using hst)
      have hIF : I.set ∈ F := by
        simp only [F, Finset.mem_filter, List.mem_toFinset, List.mem_map]
        exact ⟨⟨I, hI, rfl⟩, ⟨t, htI⟩⟩
      refine ⟨⟨I.set, hIF⟩, ?_⟩
      obtain ⟨hv, h⟩ := PointSegmentSignal.indicator_spec (J I.set) true false
      exact (h t ht).1 (by rw [hJS I.set hIF]; exact htI)
    · rintro ⟨i, hi⟩
      obtain ⟨hv, h⟩ := PointSegmentSignal.indicator_spec (J i.1) true false
      have hx : t ∈ (J i.1).set := by
        by_contra hx
        rw [(h t ht).2 hx] at hi
        exact absurd hi (by simp)
      exact hrun i.1 i.2 t ht (by rw [← hJS i.1 i.2]; exact hx)
  · -- any other decomposition has a unitary signal for each run, and no two share one
    choose p hp' using fun i : ↥F => hJne i.1 i.2
    have hordS : ∀ i : ↥F, i.1.OrdConnected := fun i => by
      rw [← hJS i.1 i.2]; exact STLInterval.set_ordConnected _
    have hex : ∀ i : ↥F, ∃ j, p i ∈ (K j).set := fun i => by
      have hst := hrun i.1 i.2 (p i) (hnnS i.1 i.2 _ (hp' i)) (hp' i)
      obtain ⟨j, hj⟩ := (hcov' _ (hnnS i.1 i.2 _ (hp' i))).1 hst
      exact ⟨j, ((hK j) _ (hnnS i.1 i.2 _ (hp' i))).1 hj⟩
    choose g hg using hex
    -- two runs sharing a unitary signal are connected through times where `s` is `true`
    have hshare : ∀ i i' : ↥F, g i = g i' → p i' ∈ i.1 := by
      intro i i' hgg
      have hK1 : p i ∈ (K (g i)).set := hg i
      have hK2 : p i' ∈ (K (g i)).set := hgg ▸ hg i'
      refine hmaxS i.1 i.2 (p i) (hp' i) (p i') (hnnS i'.1 i'.2 _ (hp' i')) fun t ht h1 h2 => ?_
      have hord : (K (g i)).set.OrdConnected := STLInterval.set_ordConnected _
      have hmem : t ∈ (K (g i)).set := hord.uIcc_subset hK1 hK2 ⟨h1, h2⟩
      exact (hcov' t ht).2 ⟨g i, ((hK (g i)) t ht).2 hmem⟩
    -- two maximal runs that meet are equal
    have hsub : ∀ i i' : ↥F, p i ∈ i'.1 → i.1 ⊆ i'.1 := by
      intro i i' hpi q hq
      refine hmaxS i'.1 i'.2 (p i) hpi q (hnnS i.1 i.2 _ hq) fun t ht h1 h2 => ?_
      exact hrun i.1 i.2 t ht ((hordS i).uIcc_subset (hp' i) hq ⟨h1, h2⟩)
    have hinj : Function.Injective g := fun i i' hgg =>
      Subtype.ext (Set.Subset.antisymm (hsub i i' (hshare i' i hgg.symm))
        (hsub i' i (hshare i i' hgg)))
    exact Fintype.card_le_of_injective g hinj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
