module

public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# Under Eq. (5), the solutions of an s-face are on the edges of its border vertex

[1, Cor. 6.3 (2)]: for `j < n` and Eq. (5), `Σ_{i≤j} vᵢ ≤ α < b_{j+1} + Σ_{i≤j} vᵢ`, the solutions
of the face `F = {v₁} × … × {v_j} × [0, b_{j+1}] × … × [0, bₙ]` are found on the edges at its
border vertex `w = (v₁, …, v_j, 0, …, 0)`: the vertices of `F ∩ {Σᵢ xᵢ = α}` are exactly the
points `w` with one coordinate `k > j` raised to `α - Σ_{i≤j} vᵢ`, and when that is `0`, `w`
itself, the unique solution. Every free coordinate stays below `b_{j+1} ≤ b_k`, the box ordered.

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

/-- Changing coordinate `i` of `v` from `0` to `a` adds `a` to the sum. -/
theorem aux_sum_update_zero'' {v : Vec ℝ n} {i : Fin n} {a : ℝ} (hvi : v i = 0) :
    ∑ k, Function.update v i a k = ∑ k, v k + a := by -- --- PROOF ---
  have : ∀ k, Function.update v i a k = v k + if k = i then a else 0 := fun k => by
    by_cases hk : k = i
    · subst hk; simp [hvi]
    · simp [hk]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.extremePoints_face_eq5 {b : Vec ℝ n} (hb : Monotone b) (hb0 : ∀ i, 0 ≤ b i)
    {j : ℕ} (hj : j < n) (p : Fin n → Bool) {α : ℝ}
    (h5 : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
        (fun i => if (i : ℕ) < j then p i else false) i ≤ α ∧
      α < b ⟨j, hj⟩ + ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
        (fun i => if (i : ℕ) < j then p i else false) i) : -- --- STMT ---
    let w := (⟨0, b⟩ : Interval (Vec ℝ n)).corner fun i => if (i : ℕ) < j then p i else false
    let F : Interval (Vec ℝ n) := ⟨w, fun i => if (i : ℕ) < j then w i else b i⟩
    Set.extremePoints ℝ (F.construct ∩ Interval.hyperplane 1 α) =
      {x | ∃ k : Fin n, j ≤ (k : ℕ) ∧
        x = Function.update w k (α - ∑ i, w i)} := by -- --- PROOF ---
  intro w F
  set β := α - ∑ i, w i with hβ
  have hβ0 : 0 ≤ β := by linarith [h5.1]
  have hβb : β < b ⟨j, hj⟩ := by linarith [h5.2]
  have hwfree : ∀ k : Fin n, j ≤ (k : ℕ) → w k = 0 := fun k hk => by
    simp [w, Interval.corner, show ¬ (k : ℕ) < j by omega]
  have hbk : ∀ k : Fin n, j ≤ (k : ℕ) → β < b k := fun k hk =>
    lt_of_lt_of_le hβb (hb (show (⟨j, hj⟩ : Fin n) ≤ k from by simp only [Fin.le_def]; omega))
  have hplane : ∀ x : Vec ℝ n, x ∈ Interval.hyperplane 1 α ↔ ∑ k, x k = α := fun x => by
    simp [Interval.hyperplane]
  ext x
  rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  constructor
  · rintro ⟨⟨hxF, hxP⟩, hedge⟩
    have hxF' : ∀ i, w i ≤ x i ∧ x i ≤ (if (i : ℕ) < j then w i else b i) := hxF
    have hfix : ∀ i : Fin n, (i : ℕ) < j → x i = w i := fun i hi => by
      have := hxF' i; simp only [hi, if_true] at this; linarith [this.1, this.2]
    -- the free coordinates are nonnegative and sum to `β`
    have hsum : ∑ i, x i = ∑ i, w i + ∑ i, (x i - w i) := by
      rw [Finset.sum_sub_distrib]; ring
    have hfree : ∑ i, (x i - w i) = β := by rw [(hplane x).mp hxP] at hsum; linarith
    have hnn : ∀ i, 0 ≤ x i - w i := fun i => by linarith [(hxF' i).1]
    -- a free coordinate at `bₖ` would already exceed `β`
    have hlt : ∀ k : Fin n, j ≤ (k : ℕ) → x k < b k := fun k hk => by
      have hle : x k - w k ≤ β := hfree ▸ Finset.single_le_sum (fun i _ => hnn i)
        (Finset.mem_univ k)
      rw [hwfree k hk] at hle; linarith [hbk k hk]
    by_cases hall : ∀ k : Fin n, j ≤ (k : ℕ) → x k = 0
    · have hxw : x = w := funext fun i => by
        by_cases hi : (i : ℕ) < j
        · exact hfix i hi
        · rw [hall i (by omega), hwfree i (by omega)]
      have hβ0' : β = 0 := by rw [← hfree, hxw]; simp
      refine ⟨⟨j, hj⟩, le_rfl, ?_⟩
      rw [hxw, hβ0']
      funext i
      by_cases hi : i = ⟨j, hj⟩
      · subst hi; simp [hwfree ⟨j, hj⟩ le_rfl]
      · rw [Function.update_of_ne hi]
    · simp only [not_forall] at hall
      obtain ⟨k, hk, hxk⟩ := hall
      -- one free coordinate inside: every other is at a bound, which is `0`
      have hother : ∀ i, i ≠ k → x i = w i := fun i hik => by
        by_cases hi : (i : ℕ) < j
        · exact hfix i hi
        · have he := (hedge i k hik).resolve_right (by
            simp only [F, show ¬ (k : ℕ) < j by omega, if_false]
            exact not_or.mpr ⟨fun h => hxk (h.trans (hwfree k hk)), (hlt k hk).ne⟩)
          simp only [F, hi, if_false] at he
          rcases he with h | h
          · exact h
          · exact absurd h (hlt i (by omega)).ne
      -- so `x` is `w` with coordinate `k` raised, by `β` since `x` is on the plane
      have hxu : x = Function.update w k (x k) := funext fun i => by
        by_cases hik : i = k
        · subst hik; simp
        · rw [Function.update_of_ne hik, hother i hik]
      refine ⟨k, hk, ?_⟩
      have hxkβ : x k = β := by
        have := (hplane x).mp hxP
        rw [hxu, aux_sum_update_zero'' (hwfree k hk)] at this
        linarith
      rw [hxu, hxkβ]
  -- each raised `w` is in `F`, on the plane, and on an edge
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨fun i => ?_, (hplane _).mpr ?_⟩, fun i i' hii' => ?_⟩
    · change w i ≤ Function.update w k β i ∧
        Function.update w k β i ≤ (if (i : ℕ) < j then w i else b i)
      by_cases hik : i = k
      · subst hik
        simp only [Function.update_self, show ¬ (i : ℕ) < j by omega, if_false,
          hwfree i hk]
        exact ⟨hβ0, (hbk i hk).le⟩
      · rw [Function.update_of_ne hik]
        by_cases hi : (i : ℕ) < j
        · simp [hi]
        · simp only [hi, if_false, hwfree i (by omega)]
          exact ⟨le_rfl, hb0 i⟩
    -- on the plane: raising coordinate `k` by `β` adds `β`
    · rw [aux_sum_update_zero'' (hwfree k hk)]; ring
    · -- every coordinate but `k` is `w`'s, the lower bound of `F`
      by_cases hik : i = k
      · right; left
        rw [Function.update_of_ne (fun h => hii' (hik.trans h.symm))]
      · left; left
        rw [Function.update_of_ne hik]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
