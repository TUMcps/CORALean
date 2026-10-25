module

public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNStepSpec
public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumAddLe
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumUpdate
public import Mathlib.Data.Nat.Find
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `EXPLORE BN` visits every border vertex

[1, Alg. 2] reaches every vertex `v` below `Σᵢ xᵢ = α` from which a solution is found: one on
the plane, or a border vertex, [1, Def. 4], `vₘ = 0` and `Σᵢ vᵢ ≤ α < bₘ + Σᵢ vᵢ`. Within the
face `(p₁, …, p_j, *, …, *)` such a vertex is either the visited `w = (…, b_{j+1}, …, b_k, 0, …)`
— above it every vertex of `V(v')` is above the plane, `b` being ordered, [1, Lemma 6.1] — or
lies in a piece of the partition [1, Lemma 6.2] the search descends into. Needs `b` ordered and
positive.

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

open Classical in
theorem Interval.mem_exploreBNVisits {b : Vec ℝ n} {α : ℝ} (hb : Monotone b)
    (hb0 : ∀ i, 0 < b i) : -- --- CONCL ---
    ∀ (j : ℕ) (p : Fin n → Bool), j ≤ n →
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (fun i => if (i : ℕ) < j then p i else false) i
        ≤ α →
      ∀ l ∈ Interval.prefixFace j p, ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i ≤ α →
        (∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i = α ∨
          ∃ m, l m = false ∧ α < ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + b m) →
        l ∈ Interval.exploreBNVisits b α j p := by -- --- PROOF ---
  have hb0' : ∀ i, 0 ≤ b i := fun i => (hb0 i).le
  intro j
  induction hm : n - j using Nat.strong_induction_on generalizing j with
  | _ m ih =>
  intro p hj hP l hl hlS hrel
  obtain ⟨hmono, hjk, hkn, hPk, hnext⟩ := Interval.exploreBN_step_spec b α j p hj hb0' hP
  rw [Interval.exploreBNVisits]
  simp only at hmono hjk hkn hPk hnext ⊢
  set k := max j (Nat.findGreatest (fun k => ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
    (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)) x ≤ α) n) with hkdef
  set w : Fin n → Bool := fun i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k) with hwdef
  by_cases hA : ∀ m : Fin n, j ≤ (m : ℕ) → (m : ℕ) < k → l m = true
  · -- `l` raises everything `w` raises; raising more would put it above the plane
    refine List.mem_cons.mpr (Or.inl (funext fun m => ?_))
    by_cases h1 : (m : ℕ) < j
    · simp [w, h1, hl m h1]
    by_cases h2 : (m : ℕ) < k
    · simp [w, h1, h2, hA m (by omega) h2]
    simp only [w, h1, h2, if_false, decide_false]
    by_contra hlm
    rw [Bool.not_eq_false] at hlm
    have hkn' : k < n := by omega
    apply hnext hkn'
    -- `lab (k + 1)` is `w` with coordinate `k` raised; `l` raises `m ≥ k` on top of `w`
    have hraise : (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k + 1)) =
        Function.update w ⟨k, hkn'⟩ true := by
      funext i
      by_cases hik : i = ⟨k, hkn'⟩
      · subst hik; simp [w, show ¬ k < j by omega]
      · rw [Function.update_of_ne hik]
        have : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
        by_cases hij : (i : ℕ) < j
        · simp [w, hij]
        · simp only [w, hij, if_false]
          by_cases hik' : (i : ℕ) < k <;> simp [hik'] <;> omega
    rw [hraise, Interval.corner_sum_update (by simp [w, show ¬ k < j by omega])]
    have hlw : ∀ i, w i = true → l i = true := fun i hi => by
      by_cases hij : (i : ℕ) < j
      · simp only [w, hij, if_true] at hi; rw [hl i hij]; exact hi
      · simp only [w, hij, if_false, decide_eq_true_eq] at hi; exact hA i (by omega) hi
    have hkm : b ⟨k, hkn'⟩ ≤ b m := hb (show (⟨k, hkn'⟩ : Fin n) ≤ m from by
      simp only [Fin.le_def]; omega)
    have := Interval.corner_sum_add_le hb0' hlw (m := m) (by simp [w, h1, h2]) hlm
    linarith
  · -- the first label `l` lowers below `k` puts it in a piece of the partition
    simp only [not_forall, Bool.not_eq_true] at hA
    have hQ : ∃ i, ∃ h : i < n, j ≤ i ∧ i < k ∧ l ⟨i, h⟩ = false := by
      obtain ⟨m, hjm, hmk, hlm⟩ := hA
      exact ⟨m, m.2, hjm, hmk, hlm⟩
    set i := Nat.find hQ with hidef
    obtain ⟨hin, hji, hik, hli⟩ : ∃ h : i < n, j ≤ i ∧ i < k ∧ l ⟨i, h⟩ = false := Nat.find_spec hQ
    have hmin : ∀ m : Fin n, j ≤ (m : ℕ) → (m : ℕ) < i → l m = true := fun m hjm hmi => by
      by_contra hlm
      rw [Bool.not_eq_true] at hlm
      exact Nat.find_min hQ hmi ⟨m.2, hjm, by omega, hlm⟩
    by_cases hk : k < n
    · refine List.mem_cons_of_mem _ ?_
      rw [dif_pos hk]
      refine List.mem_flatMap.mpr ⟨⟨i, List.mem_range'_1.mpr ⟨hji, by omega⟩⟩,
        List.mem_attach _ _, ?_⟩
      refine ih (n - (i + 1)) (by omega) (i + 1) rfl _ (by omega) ?_ l ?_ hlS hrel
      · -- the piece's own vertex is `lab i`, below `lab k`
        have hchild : (fun m : Fin n => if (m : ℕ) < i + 1 then
            (if (m : ℕ) = i then false else w m) else false) =
            fun m : Fin n => if (m : ℕ) < j then p m else decide ((m : ℕ) < i) := by
          funext m
          by_cases h1 : (m : ℕ) < j
          · simp [w, h1, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega]
          · by_cases h2 : (m : ℕ) < i
            · simp [w, h1, h2, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega,
                show (m : ℕ) < k by omega]
            · by_cases h3 : (m : ℕ) = i
              · simp [h3, show ¬ i < j by omega]
              · simp [h1, h2, show ¬ (m : ℕ) < i + 1 by omega]
        rw [hchild]
        exact le_trans (hmono i k (by omega)) hPk
      -- `l` is a vertex of the piece: `w` below `i`, lowered at `i`
      · intro m hm
        by_cases h3 : (m : ℕ) = i
        · have : m = ⟨i, hin⟩ := Fin.ext h3
          subst this; simpa using hli
        · simp only [h3, if_false]
          by_cases h1 : (m : ℕ) < j
          · simp [h1, hl m h1]
          · simp [h1, show (m : ℕ) < k by omega, hmin m (by omega) (by omega)]
    · -- `k = n`: every vertex of the face is below the plane, and `l` is no border vertex
      exfalso
      have hkn' : k = n := by omega
      have hlw : ∀ m, l m = true → w m = true := fun m hm => by
        by_cases h1 : (m : ℕ) < j
        · simp only [w, h1, if_true]; rw [← hl m h1]; exact hm
        · simp [w, h1, show (m : ℕ) < k by omega]
      have hwi : w ⟨i, hin⟩ = true := by simp [w, show ¬ i < j by omega, hik]
      have hgap := Interval.corner_sum_add_le hb0' hlw hli hwi
      rcases hrel with heq | ⟨m', hlm', hm'⟩
      · linarith [hb0 ⟨i, hin⟩]
      · by_cases h1 : (m' : ℕ) < j
        · have : b m' ≤ b ⟨i, hin⟩ := hb (show m' ≤ ⟨i, hin⟩ from by
            simp only [Fin.le_def]; omega)
          linarith
        · have hwm' : w m' = true := by simp [w, h1, show (m' : ℕ) < k by omega]
          have := Interval.corner_sum_add_le hb0' hlw hlm' hwm'
          linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
