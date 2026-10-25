module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

/-!
# The partition of an s-face around a sub-face

[1, Lemma 6.2]: for s-faces `s = (v₁, …, v_j, *, …, *)` and `s' = (v₁, …, v_k, *, …, *)`, `j < k`,
`V(s') ⊂ V(s)`, the sets `V(s')` and `V((v₁, …, v_{i-1}, v̄ᵢ, *, …, *))`, `i = j+1, …, k`, are a
partition of `V(s)`: a vertex of `s` either agrees with `s'` up to `k` or first differs at one
`i`. Coordinates counted from `0`: the pieces are `i ∈ [j, k)`, each fixing `i + 1` labels.

## Inputs
* `j` – index of the face
* `k` – index of the sub-face
* `p` – labels of the face
* `q` – labels of the sub-face

## Hypotheses
* `hjk` – face index at most sub-face index
* `hkn` – sub-face index at most the dimension
* `hq` – labels agree below the face index

## Conclusion
* the face splits into the sub-face and disjoint pieces

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.prefixFace_partition {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) (p q : Fin n → Bool)
    (hq : ∀ i : Fin n, (i : ℕ) < j → q i = p i) : -- --- CONCL ---
    let piece : ℕ → Set (Fin n → Bool) := fun i =>
      Interval.prefixFace (i + 1) fun m => if (m : ℕ) = i then !q m else q m
    Interval.prefixFace j p =
        Interval.prefixFace k q ∪ ⋃ i ∈ Finset.Ico j k, piece i ∧
      (∀ i ∈ Finset.Ico j k, Disjoint (Interval.prefixFace k q) (piece i)) ∧
      (∀ i ∈ Finset.Ico j k, ∀ i' ∈ Finset.Ico j k, i ≠ i' →
        Disjoint (piece i) (piece i')) := by -- --- PROOF ---
  intro piece
  refine ⟨?_, ?_, ?_⟩
  · ext l
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_Ico, exists_prop]
    constructor
    · intro hl
      by_cases hA : ∀ i : Fin n, (i : ℕ) < k → l i = q i
      · exact Or.inl hA
      · -- the first label in `[j, k)` where `l` leaves `q`
        right
        simp only [not_forall] at hA
        have hQ : ∃ i, ∃ h : i < n, i < k ∧ l ⟨i, h⟩ ≠ q ⟨i, h⟩ := by
          obtain ⟨m, hmk, hlm⟩ := hA
          exact ⟨m, m.2, hmk, hlm⟩
        set i := Nat.find hQ with hidef
        obtain ⟨hin, hik, hli⟩ : ∃ h : i < n, i < k ∧ l ⟨i, h⟩ ≠ q ⟨i, h⟩ := Nat.find_spec hQ
        have hmin : ∀ m : Fin n, (m : ℕ) < i → l m = q m := fun m hm => by
          by_contra hne
          exact Nat.find_min hQ hm ⟨m.2, by omega, hne⟩
        have hji : j ≤ i := by
          by_contra hlt
          have hij : ((⟨i, hin⟩ : Fin n) : ℕ) < j := by show i < j; omega
          exact hli ((hl ⟨i, hin⟩ hij).trans (hq ⟨i, hin⟩ hij).symm)
        -- `l` agrees with `q` below `i` and differs at `i`: it is in the piece `i`
        refine ⟨i, ⟨hji, hik⟩, fun m hm => ?_⟩
        by_cases hmi : (m : ℕ) = i
        · have : m = ⟨i, hin⟩ := Fin.ext hmi
          subst this
          simp only [if_true]
          revert hli
          cases l ⟨i, hin⟩ <;> cases q ⟨i, hin⟩ <;> simp
        · simp only [hmi, if_false]
          exact hmin m (by omega)
    · rintro (hl | ⟨i, ⟨hji, hik⟩, hl⟩) m hm
      · rw [hl m (by omega), hq m hm]
      · have := hl m (by omega)
        simp only [show (m : ℕ) ≠ i by omega, if_false] at this
        rw [this, hq m hm]
  · -- `V(s')` keeps `qᵢ`, the piece `i` flips it
    intro i hi
    rw [Finset.mem_Ico] at hi
    refine Set.disjoint_left.mpr fun l hl hl' => ?_
    have hin : i < n := by omega
    have h1 := hl ⟨i, hin⟩ hi.2
    have h2 := hl' ⟨i, hin⟩ (by simp)
    simp only [if_true] at h2
    rw [h1] at h2
    simp at h2
  · -- two pieces: the earlier flips `qᵢ`, the later keeps it
    intro i hi i' hi' hne
    rw [Finset.mem_Ico] at hi hi'
    -- order the two, then read the earlier index in both
    have key : ∀ a b, a < b → b < k → Disjoint (piece a) (piece b) := fun a b hab hbk => by
      refine Set.disjoint_left.mpr fun l hl hl' => ?_
      have han : a < n := by omega
      have h1 := hl ⟨a, han⟩ (by simp)
      have h2 := hl' ⟨a, han⟩ (by simp; omega)
      simp only [if_true] at h1
      simp only [show a ≠ b by omega, if_false] at h2
      rw [h2] at h1
      simp at h1
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i' h hi'.2
    · exact (key i' i h hi.2).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
