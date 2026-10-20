module

public import CORALean.Global.OptimalDiscard
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Algorithm A* discards optimally

[1, Thm. 2]: if the value `w` of a problem only grows with its constraints and every problem is
non-degenerate, `w(sc(F)) = w(F)` [1, Def. 4], and no problem of the tree of `discardTree` before
level `k` is without support constraints, then `optimalDiscard` returns a set of `N - k` constraints
of least value among all `N - k` of them. The leaves are reached by removing one support constraint
at a time (`aux_discardTree_succ`). A set `F \ K` with no support constraint removed has the value
of `F`, which every leaf under `F` is below; otherwise the first support constraint in `K` is
removed and the induction goes on at `F - s`, `K - s`. Without the last hypothesis the tree can die
before level `k`, and the algorithm returns nothing, though `F \ K` of value `w(∅)` exists.

## Inputs
* `D` – full constraint set
* `k` – number of constraints to discard

## Hypotheses
* `hmono` – the value grows with the constraints
* `hnd` – every problem is non-degenerate
* `hsc` – every problem before the level has a support constraint

## Conclusion
* the returned set has the right size and least value among all remaining sets

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N : ℕ} {β : Type} [LinearOrder β] (w : Finset (Fin N) → β)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_mem_supportConstraints (F : Finset (Fin N)) (l : Fin N) :
    l ∈ supportConstraints w F ↔ l ∈ F ∧ w (F.erase l) < w F := by
  simp [supportConstraints]

-- the tree under `F`, root first: one subtree for each support constraint of the root
theorem aux_discardTree_succ (F : Finset (Fin N)) (j : ℕ) :
    discardTree w F (j + 1) =
      (supportConstraints w F).flatMap fun l => discardTree w (F.erase l) j := by -- --- PROOF ---
  induction j generalizing F with
  | zero =>
    simp only [discardTree, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (List.map_eq_flatMap).trans rfl
  | succ j ih =>
    rw [discardTree, ih F, List.flatMap_assoc]
    rfl

-- a problem under the subtree of a support constraint is one level lower under `F`
theorem aux_mem_discardTree_erase {F G : Finset (Fin N)} {l : Fin N} {d : ℕ}
    (hl : l ∈ supportConstraints w F) (hG : G ∈ discardTree w (F.erase l) d) :
    G ∈ discardTree w F (d + 1) := by
  rw [aux_discardTree_succ]
  exact List.mem_flatMap.mpr ⟨l, hl, hG⟩

-- every problem at level `j` has `j` constraints fewer
theorem aux_discardTree_sub (F : Finset (Fin N)) (j : ℕ) :
    ∀ G ∈ discardTree w F j, G ⊆ F ∧ G.card + j = F.card := by -- --- PROOF ---
  induction j generalizing F with
  | zero => intro G hG; simp [discardTree] at hG; simp [hG]
  | succ j ih =>
    intro G hG
    rw [aux_discardTree_succ, List.mem_flatMap] at hG
    obtain ⟨l, hl, hG⟩ := hG
    have hlF := ((aux_mem_supportConstraints w F l).mp hl).1
    obtain ⟨h1, h2⟩ := ih (F.erase l) G hG
    refine ⟨h1.trans (Finset.erase_subset _ _), ?_⟩
    have := Finset.card_erase_add_one hlF
    omega

-- a tree whose problems all have a support constraint reaches level `j`
theorem aux_discardTree_ne_nil (j : ℕ) :
    ∀ F : Finset (Fin N), (∀ d < j, ∀ G ∈ discardTree w F d, supportConstraints w G ≠ []) →
      discardTree w F j ≠ [] := by -- --- PROOF ---
  induction j with
  | zero => intro F _; simp [discardTree]
  | succ j ih =>
    intro F hsc
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (hsc 0 (Nat.succ_pos j) F (by simp [discardTree]))
    have := ih (F.erase l) fun d hd G hG => hsc (d + 1) (by omega) G
      (aux_mem_discardTree_erase w hl hG)
    obtain ⟨G, hG⟩ := List.exists_mem_of_ne_nil _ this
    exact List.ne_nil_of_mem (aux_mem_discardTree_erase w hl hG)

-- some problem at level `j` is below `F \ K`, for any `K` of `j` constraints
theorem aux_discardTree_exists_le (D : Finset (Fin N)) (hmono : ∀ G H, G ⊆ H → w G ≤ w H)
    (hnd : ∀ G ⊆ D, w (supportConstraints w G).toFinset = w G) (j : ℕ) : -- --- CONCL ---
    ∀ F ⊆ D, ∀ K ⊆ F, K.card = j →
      (∀ d < j, ∀ G ∈ discardTree w F d, supportConstraints w G ≠ []) →
      ∃ L ∈ discardTree w F j, w L ≤ w (F \ K) := by -- --- PROOF ---
  induction j with
  | zero =>
    intro F _ K _ hK _
    obtain rfl := Finset.card_eq_zero.mp hK
    exact ⟨F, by simp [discardTree], by simp⟩
  | succ j ih =>
    intro F hFD K hKF hK hsc
    by_cases h : ∃ s ∈ K, s ∈ supportConstraints w F
    · -- remove the support constraint `s` of `F` that `K` holds
      obtain ⟨s, hsK, hs⟩ := h
      have hK' : (K.erase s).card = j := by rw [Finset.card_erase_of_mem hsK]; omega
      have hK'F : K.erase s ⊆ F.erase s := fun x hx =>
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hKF (Finset.mem_of_mem_erase hx)⟩
      obtain ⟨L, hL, hLw⟩ := ih (F.erase s) ((Finset.erase_subset _ _).trans hFD) (K.erase s) hK'F
        hK' fun d hd G hG => hsc (d + 1) (by omega) G (aux_mem_discardTree_erase w hs hG)
      have hset : F.erase s \ K.erase s = F \ K := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hxs, hxF⟩, hxK⟩
          exact ⟨hxF, fun hx => hxK ⟨hxs, hx⟩⟩
        · rintro ⟨hxF, hxK⟩
          exact ⟨⟨fun hxs => hxK (hxs ▸ hsK), hxF⟩, fun hx => hxK hx.2⟩
      exact ⟨L, aux_mem_discardTree_erase w hs hL, hset ▸ hLw⟩
    · -- no support constraint of `F` is removed: `F \ K` keeps the value of `F`
      simp only [not_exists, not_and] at h
      have hsub : (supportConstraints w F).toFinset ⊆ F \ K := fun x hx => by
        rw [List.mem_toFinset] at hx
        exact Finset.mem_sdiff.mpr
          ⟨((aux_mem_supportConstraints w F x).mp hx).1, fun hxK => h x hxK hx⟩
      have hF : w F ≤ w (F \ K) := by
        rw [← hnd F hFD]; exact hmono _ _ hsub
      obtain ⟨L, hL⟩ := List.exists_mem_of_ne_nil _ (aux_discardTree_ne_nil w (j + 1) F hsc)
      exact ⟨L, hL, (hmono _ _ ((aux_discardTree_sub w F (j + 1) L hL).1)).trans hF⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem optimalDiscard_le (D : Finset (Fin N)) (k : ℕ) (hmono : ∀ G H, G ⊆ H → w G ≤ w H)
    (hnd : ∀ G ⊆ D, w (supportConstraints w G).toFinset = w G)
    (hsc : ∀ d < k, ∀ G ∈ discardTree w D d, supportConstraints w G ≠ []) : -- --- CONCL ---
    ∃ L, optimalDiscard w D k = some L ∧ L ⊆ D ∧ L.card + k = D.card ∧
      ∀ K ⊆ D, K.card = k → w L ≤ w (D \ K) := by -- --- PROOF ---
  -- level `k` is not empty, so the least problem of it exists
  have hne := aux_discardTree_ne_nil w k D hsc
  obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp
    (mt List.argmin_eq_none.mp hne : (discardTree w D k).argmin w ≠ none)
  have hmem := List.argmin_mem hL
  obtain ⟨h1, h2⟩ := aux_discardTree_sub w D k L hmem
  refine ⟨L, hL, h1, h2, fun K hKD hK => ?_⟩
  obtain ⟨M, hM, hMw⟩ := aux_discardTree_exists_le w D hmono hnd k D subset_rfl K hKD hK hsc
  exact (List.le_of_mem_argmin hM hL).trans hMw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
