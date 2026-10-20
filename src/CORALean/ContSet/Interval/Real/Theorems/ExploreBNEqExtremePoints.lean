module

public import CORALean.ContSet.Interval.Real.Operations.ExploreBN
public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNVisitsSumLe
public import CORALean.ContSet.Interval.Real.Theorems.MemExploreBNVisits
public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `EXPLORE BN` returns exactly the vertices of the cut

[1, Alg. 2] with [1, Alg. 3] "determines all vertices" of the intersection of the ordered box
`[0, b₁] × … × [0, bₙ]` with `Σᵢ xᵢ = α`: its output is exactly the set of extreme points of
`B ∩ P`. Sound, as `FIND SOLUTIONS` adds a point on an edge from a visited vertex below the
plane (`exploreBNVisits_sum_le`); complete, as every extreme point lies on an edge
(`mem_extremePoints_inter_hyperplane_iff`) whose lower end is on the plane or a border vertex,
which the search visits (`mem_exploreBNVisits`). Needs `b` ordered and positive, as the paper
assumes, and `α ≥ 0`, which line 6 needs for its `k` and the paper does not state.

## Inputs
* `b` – upper bound vector
* `α` – level of the plane

## Hypotheses
* `hb` – bounds nondecreasing
* `hb0` – bounds positive
* `hα` – level nonnegative

## Conclusion
* the returned set is exactly the vertices of the cut

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Membership in the union line 8 accumulates. -/
theorem aux_mem_foldr_union {β γ : Type} [DecidableEq γ] (f : β → Finset γ) (L : List β)
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

/-- Changing coordinate `i` of `v` from `0` to `a` adds `a` to the sum. -/
theorem aux_sum_update_zero {v : Vec ℝ n} {i : Fin n} {a : ℝ} (hvi : v i = 0) : -- --- CONCL ---
    ∑ k, Function.update v i a k = ∑ k, v k + a := by -- --- PROOF ---
  have : ∀ k, Function.update v i a k = v k + if k = i then a else 0 := fun k => by
    by_cases hk : k = i
    · subst hk; simp [hvi]
    · simp [hk]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exploreBN_eq_extremePoints {b : Vec ℝ n} {α : ℝ} (hb : Monotone b)
    (hb0 : ∀ i, 0 < b i) (hα : 0 ≤ α) : -- --- CONCL ---
    ↑(Interval.exploreBN b α) = Set.extremePoints ℝ
      ((⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩ Interval.hyperplane 1 α) := by -- --- PROOF ---
  classical
  have hb0' : ∀ i, 0 ≤ b i := fun i => (hb0 i).le
  have hcorner : ∀ (l : Fin n → Bool) k,
      (⟨0, b⟩ : Interval (Vec ℝ n)).corner l k = if l k then b k else 0 := fun l k => rfl
  have hplane : ∀ x : Vec ℝ n, x ∈ Interval.hyperplane 1 α ↔ ∑ k, x k = α := fun x => by
    simp [Interval.hyperplane]
  have hbox : ∀ x : Vec ℝ n, x ∈ (⟨0, b⟩ : Interval (Vec ℝ n)).construct ↔
      ∀ k, 0 ≤ x k ∧ x k ≤ b k := fun x => Iff.rfl
  -- the root face `(*, …, *)` has its vertex `0` below the plane
  have hroot : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun i => if (i : ℕ) < 0 then (fun _ => false) i else false) i ≤ α := by
    simpa [hcorner] using hα
  ext x
  rw [Interval.exploreBN, Finset.mem_coe, aux_mem_foldr_union,
    Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  constructor
  · -- sound: a point `FIND SOLUTIONS` adds is in the box, on the plane, on an edge
    rintro ⟨w, hw, hx⟩
    have hwS := Interval.exploreBNVisits_sum_le hb0' 0 _ (Nat.zero_le n) hroot w hw
    unfold Interval.findSolutions at hx
    simp only at hx
    split_ifs at hx with h0
    · rw [Finset.mem_singleton] at hx
      subst hx
      refine ⟨⟨(hbox _).mpr fun k => ?_, (hplane _).mpr (by linarith)⟩, fun i j _ => ?_⟩
      · rw [hcorner]; split_ifs <;> simp [hb0' k]
      · left; rw [hcorner]; split_ifs <;> simp
    -- a raised point: `α' ∈ [0, bᵢ)` at coordinate `i`, the rest at a bound
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hib, hvi⟩ := (Finset.mem_filter.mp hi).2
      have hpos : 0 ≤ α - ∑ k, (⟨0, b⟩ : Interval (Vec ℝ n)).corner w k := by linarith
      refine ⟨⟨(hbox _).mpr fun k => ?_, (hplane _).mpr ?_⟩, fun k k' hkk' => ?_⟩
      · by_cases hki : k = i
        · subst hki; simp only [Function.update_self]; exact ⟨hpos, hib.le⟩
        · rw [Function.update_of_ne hki, hcorner]; split_ifs <;> simp [hb0' k]
      · rw [aux_sum_update_zero hvi]; ring
      · by_cases hki : k = i
        · right
          have hk'i : k' ≠ i := fun h => hkk' (hki.trans h.symm)
          rw [Function.update_of_ne hk'i, hcorner]; split_ifs <;> simp
        · left
          rw [Function.update_of_ne hki, hcorner]; split_ifs <;> simp
  · -- complete: the lower end of the edge an extreme point lies on is visited
    rintro ⟨⟨hxB, hxP⟩, hedge⟩
    have hxB' := (hbox x).mp hxB
    have hxP' := (hplane x).mp hxP
    by_cases hint : ∃ m, x m ≠ 0 ∧ x m ≠ b m
    · obtain ⟨m, hm0, hmb⟩ := hint
      have hbd : ∀ k, k ≠ m → x k = 0 ∨ x k = b k := fun k hk => by
        have := (hedge k m hk).resolve_right (by simp [hm0, hmb])
        simpa using this
      let l : Fin n → Bool := fun k => if k = m then false else decide (x k = b k)
      have hlc : ∀ k, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l k = if k = m then 0 else x k :=
        fun k => by
          rw [hcorner]
          by_cases hkm : k = m
          · simp [l, hkm]
          · rcases hbd k hkm with h | h
            · by_cases hxb : x k = b k
              · simp [l, hkm, hxb]
              · simp [l, hkm, h, (hb0 k).ne]
            · simp [l, hkm, h]
      -- `x` is the corner below it with coordinate `m` raised to `xₘ`
      have hxu : x = Function.update ((⟨0, b⟩ : Interval (Vec ℝ n)).corner l) m (x m) := by
        funext k
        by_cases hkm : k = m
        · subst hkm; simp
        · rw [Function.update_of_ne hkm, hlc]; simp [hkm]
      have hlm0 : (⟨0, b⟩ : Interval (Vec ℝ n)).corner l m = 0 := by rw [hlc]; simp
      have hS : ∑ k, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l k = α - x m := by
        have := aux_sum_update_zero (a := x m) hlm0
        rw [← hxu] at this
        linarith
      have hxm : 0 < x m := lt_of_le_of_ne (hxB' m).1 (Ne.symm hm0)
      have hxm' : x m < b m := lt_of_le_of_ne (hxB' m).2 hmb
      have hlv := Interval.mem_exploreBNVisits hb hb0 0 (fun _ => false) (Nat.zero_le n) hroot l
        (fun _ h => absurd h (Nat.not_lt_zero _)) (by linarith)
        (Or.inr ⟨m, by simp [l], by linarith⟩)
      -- `FIND SOLUTIONS` raises `m` by `α' = xₘ`
      refine ⟨l, hlv, ?_⟩
      unfold Interval.findSolutions
      simp only
      rw [if_neg (by rw [hS]; linarith), Finset.mem_image]
      refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS]; linarith, hlm0⟩, ?_⟩
      rw [hS, sub_sub_cancel]
      exact hxu.symm
    -- no coordinate inside: `x` is a vertex on the plane, visited, and its own solution
    · simp only [not_exists, not_and, not_not] at hint
      let l : Fin n → Bool := fun k => decide (x k = b k)
      have hlx : (⟨0, b⟩ : Interval (Vec ℝ n)).corner l = x := by
        funext k
        rw [hcorner]
        by_cases hxb : x k = b k
        · simp [l, hxb]
        · simp [l, hxb]
          by_contra h0
          exact hxb (hint k (Ne.symm h0))
      have hlv := Interval.mem_exploreBNVisits hb hb0 0 (fun _ => false) (Nat.zero_le n) hroot l
        (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [hlx]; linarith)
        (Or.inl (by rw [hlx]; exact hxP'))
      refine ⟨l, hlv, ?_⟩
      unfold Interval.findSolutions
      simp only
      rw [if_pos (by rw [hlx]; linarith), Finset.mem_singleton, hlx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
