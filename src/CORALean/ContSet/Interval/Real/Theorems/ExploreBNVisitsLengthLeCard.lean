module

public import CORALean.ContSet.Interval.Real.Operations.ExploreBN
public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNStepSpec
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumMono
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumUpdate
public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# The loop of `EXPLORE BN` runs at most once per solution

[1, Sec. 6.2]: by [1, Lemma 6.5] every s-face pushed onto the stack produces a solution, so the
loop runs at most `m` times, `m` the number of solutions, and with `O(n)` per iteration the
algorithm is `O(nm)`. The count, proved: the visited vertices are distinct, each one's
`FIND SOLUTIONS` is nonempty, and no solution comes from two of them (it determines its lower
vertex), so there are at most as many visits as solutions — when the plane meets the box,
`α ≤ Σᵢ bᵢ`; above it the root still runs once, for `m = 0`. The `O(n)` per iteration is a
running cost, which a definition does not state.

## Inputs
* `b` – upper bound vector
* `α` – level of the plane

## Hypotheses
* `hb0` – bounds positive
* `hα` – level nonnegative
* `hαb` – level at most the sum of the bounds

## Conclusion
* the number of loop visits is at most the number of solutions

## References

* [1] [C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science,
      2009.](../../../../../../references/2009/lara-infocomp-hyperbox-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The visits of a face are vertices of the face. -/
private theorem aux_visits_subset {b : Vec ℝ n} {α : ℝ} : -- --- CONCL ---
    ∀ (j : ℕ) (p : Fin n → Bool), ∀ w ∈ Interval.exploreBNVisits b α j p,
      w ∈ Interval.prefixFace j p := by -- --- PROOF ---
  intro j
  induction hm : n - j using Nat.strong_induction_on generalizing j with
  | _ m ih =>
  intro p w hw
  rw [Interval.exploreBNVisits] at hw
  simp only at hw
  rcases List.mem_cons.mp hw with rfl | hw
  · intro i hi; simp [hi]
  · split_ifs at hw with hk
    · obtain ⟨⟨i, hi⟩, -, hwi⟩ := List.mem_flatMap.mp hw
      have hi' := List.mem_range'_1.mp hi
      have hsub := ih (n - (i + 1)) (by omega) (i + 1) rfl _ w hwi
      intro m hmj
      have := hsub m (by omega)
      simp only [show (m : ℕ) ≠ i by omega, if_false, hmj, if_true] at this
      exact this
    · simp at hw

/-- The visits are distinct: the pieces of a partition are disjoint and miss `w`. -/
private theorem aux_visits_nodup {b : Vec ℝ n} {α : ℝ} : -- --- CONCL ---
    ∀ (j : ℕ) (p : Fin n → Bool),
      (Interval.exploreBNVisits b α j p).Nodup := by -- --- PROOF ---
  intro j
  induction hm : n - j using Nat.strong_induction_on generalizing j with
  | _ m ih =>
  intro p
  rw [Interval.exploreBNVisits]
  simp only
  set k := max j (Nat.findGreatest (fun k => ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
    (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)) x ≤ α) n) with hkdef
  split_ifs with hk
  · rw [List.nodup_cons]
    refine ⟨fun hw => ?_, ?_⟩
    · -- `w` raises every `i ∈ [j, k)`, the piece `i` lowers it
      obtain ⟨⟨i, hi⟩, -, hwi⟩ := List.mem_flatMap.mp hw
      have hi' := List.mem_range'_1.mp hi
      have := aux_visits_subset (b := b) (α := α) (i + 1) _ _ hwi ⟨i, by omega⟩ (by simp)
      simp only [if_true] at this
      simp [show ¬ i < j by omega, show i < k by omega] at this
    · refine List.nodup_flatMap.mpr ⟨fun i _ => ih _ (by have := List.mem_range'_1.mp i.2; omega)
        _ rfl _, ?_⟩
      -- the earlier piece lowers `a`, the later keeps it raised
      have key : ∀ a c : ℕ, a ∈ List.range' j (k - j) → c ∈ List.range' j (k - j) → a < c →
          List.Disjoint (Interval.exploreBNVisits b α (a + 1) fun m =>
              if (m : ℕ) = a then false else if (m : ℕ) < j then p m else decide ((m : ℕ) < k))
            (Interval.exploreBNVisits b α (c + 1) fun m =>
              if (m : ℕ) = c then false else
                if (m : ℕ) < j then p m else decide ((m : ℕ) < k)) := by
        -- a common visit would agree with both pieces at `a`
        intro a c ha hc hac w hw1 hw2
        have ha' := List.mem_range'_1.mp ha
        have hc' := List.mem_range'_1.mp hc
        have h1 := aux_visits_subset (b := b) (α := α) (a + 1) _ _ hw1 ⟨a, by omega⟩ (by simp)
        have h2 := aux_visits_subset (b := b) (α := α) (c + 1) _ _ hw2 ⟨a, by omega⟩
          (by simp; omega)
        simp only [if_true] at h1
        simp only [show a ≠ c by omega, if_false] at h2
        rw [h1] at h2
        simp [show ¬ a < j by omega, show a < k by omega] at h2
      refine (List.nodup_attach.mpr (List.nodup_range' (s := j) (n := k - j))).pairwise_of_forall_ne
        fun a _ c _ hac => ?_
      rcases lt_or_gt_of_ne (fun h => hac (Subtype.ext h)) with h | h
      · exact key a.1 c.1 a.2 c.2 h
      · exact (key c.1 a.1 c.2 a.2 h).symm
  · exact List.nodup_singleton _

/-- `FIND SOLUTIONS` of every visit returns something, given that the plane meets the box. -/
private theorem aux_visits_nonempty {b : Vec ℝ n} {α : ℝ} (hb0 : ∀ i, 0 < b i) : -- --- CONCL ---
    ∀ (j : ℕ) (p : Fin n → Bool), (hj : j ≤ n) →
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (fun i => if (i : ℕ) < j then p i else false) i
        ≤ α →
      (j = 0 → α ≤ ∑ i, b i) →
      (∀ h : 0 < j, p ⟨j - 1, by omega⟩ = false ∧ α < ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
        (fun m => if (m : ℕ) < j - 1 then p m else true) i) →
      ∀ w ∈ Interval.exploreBNVisits b α j p,
        (Interval.findSolutions b α
          ((⟨0, b⟩ : Interval (Vec ℝ n)).corner w)).Nonempty := by -- --- PROOF ---
  have hb0' : ∀ i, 0 ≤ b i := fun i => (hb0 i).le
  -- a vertex below the plane with a raisable coordinate reaching it has a solution
  have hfs : ∀ (v : Fin n → Bool) (m : Fin n), v m = false →
      α - ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner v i < b m →
      (Interval.findSolutions b α ((⟨0, b⟩ : Interval (Vec ℝ n)).corner v)).Nonempty := by
    intro v m hvm hlt
    unfold Interval.findSolutions
    simp only
    split_ifs with h0
    · exact Finset.singleton_nonempty _
    · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hlt,
        by simp [Interval.corner, hvm]⟩)⟩
  -- by strong induction on the undefined labels, as the recursion runs
  intro j
  induction hm : n - j using Nat.strong_induction_on generalizing j with
  | _ m ih =>
  intro p hj hP hroot hinv w hw
  obtain ⟨hmono, hjk, hkn, hPk, hnext⟩ := Interval.exploreBN_step_spec b α j p hj hb0' hP
  rw [Interval.exploreBNVisits] at hw
  simp only at hw hmono hjk hkn hPk hnext
  set k := max j (Nat.findGreatest (fun k => ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
    (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)) x ≤ α) n) with hkdef
  rcases List.mem_cons.mp hw with rfl | hw
  · by_cases hk : k < n
    · -- line 6 stopped at `k`: coordinate `k + 1` reaches the plane
      refine hfs _ ⟨k, hk⟩ (by simp [show ¬ k < j by omega]) ?_
      have hraise : (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k + 1)) =
          Function.update (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k))
            ⟨k, hk⟩ true := by
        funext i
        by_cases hik : i = ⟨k, hk⟩
        · subst hik; simp [show ¬ k < j by omega]
        · rw [Function.update_of_ne hik]
          have : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
          by_cases hij : (i : ℕ) < j
          · simp [hij]
          · simp only [hij, if_false]
            by_cases hik' : (i : ℕ) < k <;> simp [hik'] <;> omega
      have h := not_le.mp (hnext hk)
      rw [hraise, Interval.corner_sum_update (by simp [show ¬ k < j by omega])] at h
      linarith
    · by_cases hj0 : j = 0
      · -- the root raised everything: `w = b`, on the plane since `α ≤ Σᵢ bᵢ`
        subst hj0
        have hS : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
            (fun i : Fin n => if (i : ℕ) < 0 then p i else decide ((i : ℕ) < k)) i = ∑ i, b i :=
          Finset.sum_congr rfl fun i _ => by simp [Interval.corner, show (i : ℕ) < k by omega]
        unfold Interval.findSolutions
        simp only
        rw [if_pos (by rw [hS]; linarith [hroot rfl])]
        exact Finset.singleton_nonempty _
      · -- the face raised everything after `j`: its own lowered `j - 1` reaches the plane
        obtain ⟨hpj, hlt⟩ := hinv (by omega)
        refine hfs _ ⟨j - 1, by omega⟩ (by simp [show j - 1 < j by omega, hpj]) ?_
        have hfull : (fun m : Fin n => if (m : ℕ) < j - 1 then p m else true) =
            Function.update (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k))
              ⟨j - 1, by omega⟩ true := by
          funext m
          by_cases hmj : m = ⟨j - 1, by omega⟩
          · subst hmj; simp
          · rw [Function.update_of_ne hmj]
            have : (m : ℕ) ≠ j - 1 := fun h => hmj (Fin.ext h)
            by_cases h1 : (m : ℕ) < j - 1
            · simp [h1, show (m : ℕ) < j by omega]
            · simp [h1, show ¬ (m : ℕ) < j by omega, show (m : ℕ) < k by omega]
        rw [hfull, Interval.corner_sum_update (by simp [show j - 1 < j by omega, hpj])] at hlt
        linarith
  · split_ifs at hw with hk
    · obtain ⟨⟨i, hi⟩, -, hwi⟩ := List.mem_flatMap.mp hw
      have hi' := List.mem_range'_1.mp hi
      refine ih (n - (i + 1)) (by omega) (i + 1) rfl _ (by omega) ?_ (by omega) ?_ w hwi
      · -- the piece's own vertex is `lab i`, below `lab k`
        have hchild : (fun m : Fin n => if (m : ℕ) < i + 1 then
            (if (m : ℕ) = i then false else if (m : ℕ) < j then p m else decide ((m : ℕ) < k))
            else false) = fun m : Fin n => if (m : ℕ) < j then p m else decide ((m : ℕ) < i) := by
          funext m
          by_cases h1 : (m : ℕ) < j
          · simp [h1, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega]
          · by_cases h2 : (m : ℕ) < i
            · simp [h1, h2, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega,
                show (m : ℕ) < k by omega]
            · by_cases h3 : (m : ℕ) = i
              · simp [h3, show ¬ i < j by omega]
              · simp [h1, h2, show ¬ (m : ℕ) < i + 1 by omega]
        rw [hchild]
        exact le_trans (hmono i k (by omega)) hPk
      · -- the piece lowered `i`, and raising it with all after passes `lab (k + 1)`
        intro _
        refine ⟨by simp, ?_⟩
        refine lt_of_lt_of_le (not_le.mp (hnext hk)) (Interval.corner_sum_mono hb0' fun m hm => ?_)
        simp only [Nat.add_sub_cancel]
        by_cases h1 : (m : ℕ) < j
        · simp only [h1, if_true] at hm
          simp [h1, show (m : ℕ) < i by omega, show (m : ℕ) ≠ i by omega, hm]
        · simp only [h1, if_false, decide_eq_true_eq] at hm
          by_cases h2 : (m : ℕ) < i
          · simp [h1, h2, show (m : ℕ) ≠ i by omega, show (m : ℕ) < k by omega]
          · simp [h2]
    · simp at hw

/-- A solution determines the vertex it was found from. -/
private theorem aux_decode {b : Vec ℝ n} {α : ℝ} (hb0 : ∀ i, 0 < b i) {w : Fin n → Bool}
    {x : Vec ℝ n} (hx : x ∈ Interval.findSolutions b α ((⟨0, b⟩ : Interval (Vec ℝ n)).corner w))
    : -- --- CONCL ---
    (fun k => decide (x k = b k)) = w := by -- --- PROOF ---
  have hc : ∀ k, decide ((⟨0, b⟩ : Interval (Vec ℝ n)).corner w k = b k) = w k := fun k => by
    simp only [Interval.corner]
    cases w k <;> simp [(hb0 k).ne]
  unfold Interval.findSolutions at hx
  simp only at hx
  split_ifs at hx with h0
  · rw [Finset.mem_singleton] at hx
    subst hx; exact funext hc
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hib, hvi⟩ := (Finset.mem_filter.mp hi).2
    funext k
    by_cases hki : k = i
    · subst hki
      rw [← hc k, hvi]
      simp only [Function.update_self]
      simp [hib.ne, (hb0 k).ne]
    · rw [Function.update_of_ne hki]; exact hc k

/-- Membership in the union line 8 accumulates. -/
private theorem aux_mem_foldr_union_iff {β γ : Type} [DecidableEq γ] (f : β → Finset γ) (L : List β)
    (x : γ) : -- --- CONCL ---
    x ∈ L.foldr (fun w acc => f w ∪ acc) ∅ ↔ ∃ w ∈ L, x ∈ f w := by -- --- PROOF ---
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨w', hw', h⟩)
      · exact ⟨w, Or.inl rfl, h⟩
      · exact ⟨w', Or.inr hw', h⟩
    · rintro ⟨w', hw' | hw', h⟩
      · exact Or.inl (hw' ▸ h)
      · exact Or.inr ⟨w', hw', h⟩

/-- A nodup list of nonempty, decodable blocks has at most as many entries as their union. -/
private theorem aux_length_le_card {β γ : Type} [DecidableEq γ] (f : β → Finset γ) (g : γ → β)
    (L : List β) (hnd : L.Nodup) (hne : ∀ w ∈ L, (f w).Nonempty)
    (hg : ∀ w ∈ L, ∀ x ∈ f w, g x = w) : -- --- CONCL ---
    L.length ≤ (L.foldr (fun w acc => f w ∪ acc) ∅).card := by -- --- PROOF ---
  induction L with
  | nil => simp
  | cons w L ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.length_cons, List.foldr_cons]
    have hdisj : Disjoint (f w) (L.foldr (fun w acc => f w ∪ acc) ∅) := by
      rw [Finset.disjoint_left]
      intro x hx hxL
      -- `x` came from some later `w'`, which decodes to `w`
      have : ∃ w' ∈ L, x ∈ f w' := (aux_mem_foldr_union_iff f L x).mp hxL
      obtain ⟨w', hw', hx'⟩ := this
      have h1 := hg w (by simp) x hx
      have h2 := hg w' (by simp [hw']) x hx'
      exact hnd.1 (h1 ▸ h2 ▸ hw')
    rw [Finset.card_union_of_disjoint hdisj]
    have hw := (hne w (by simp)).card_pos
    have := ih hnd.2 (fun u hu => hne u (by simp [hu])) (fun u hu => hg u (by simp [hu]))
    omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exploreBNVisits_length_le_card {b : Vec ℝ n} {α : ℝ} (hb0 : ∀ i, 0 < b i)
    (hα : 0 ≤ α) (hαb : α ≤ ∑ i, b i) : -- --- CONCL ---
    (Interval.exploreBNVisits b α 0 fun _ => false).length ≤
      (Interval.exploreBN b α).card := by -- --- PROOF ---
  classical
  have hroot : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun i => if (i : ℕ) < 0 then (fun _ => false) i else false) i ≤ α := by
    simpa [Interval.corner] using hα
  unfold Interval.exploreBN
  exact aux_length_le_card
    (fun w => Interval.findSolutions b α ((⟨0, b⟩ : Interval (Vec ℝ n)).corner w))
    (fun x k => decide (x k = b k)) _ (aux_visits_nodup 0 _)
    (aux_visits_nonempty hb0 0 _ (Nat.zero_le n) hroot (fun _ => hαb)
      (fun h => absurd h (lt_irrefl 0)))
    (fun w _ x hx => aux_decode hb0 hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
