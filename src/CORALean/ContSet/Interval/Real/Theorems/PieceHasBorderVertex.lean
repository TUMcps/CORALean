module

public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNStepSpec
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumMono
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumUpdate
public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane

@[expose] public section

/-!
# Every piece of the partition reaches a solution

[1, Lemma 6.5]: with `k < n` from line 6 of [1, Alg. 2], so that `s' = (v₁, …, v_j, b_{j+1}, …,
b_k, *, …, *)` has a single border node, each element of `P(s, s')` has at least one solution.
Read as the output specification of Alg. 2 reads it, "solutions adjacent to or at" the vertices:
every piece `(v₁, …, v_j, b_{j+1}, …, b_{i-1}, 0, *, …, *)` holds a vertex `u` below the plane
with a raisable `uₘ = 0`, `α < Σᵢ uᵢ + bₘ`, so the edge it raises meets the plane. Its own face
need not, `Interval.piece_solution_counterexample`. Neither needs the box ordered.

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


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem Interval.piece_has_border_vertex {b : Vec ℝ n} (hb0 : ∀ i, 0 ≤ b i)
    {α : ℝ} {j k : ℕ} (p : Fin n → Bool) (hkn : k < n)
    (hPk : ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)) x ≤ α)
    (hnext : α < ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k + 1)) x)
    {i : ℕ} (hji : j ≤ i) (hik : i < k) :
    ∃ u ∈ Interval.prefixFace (i + 1) (fun m => if (m : ℕ) = i then false else
        if (m : ℕ) < j then p m else decide ((m : ℕ) < k)),
      ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner u x ≤ α ∧
        ∃ m, u m = false ∧
          α < ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner u x + b m := by -- --- PROOF ---
  have hb0' : ∀ i, 0 ≤ b i := hb0
  set p' : Fin n → Bool := fun m => if (m : ℕ) = i then false else
    if (m : ℕ) < j then p m else decide ((m : ℕ) < k) with hp'
  -- the piece's own vertex is `lab i`, below `lab k`, so line 6 applies to it
  have hpre : (fun m : Fin n => if (m : ℕ) < i + 1 then p' m else false) =
      fun m : Fin n => if (m : ℕ) < j then p m else decide ((m : ℕ) < i) := by
    funext m
    by_cases h1 : (m : ℕ) < j
    · simp [p', h1, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega]
    · by_cases h2 : (m : ℕ) < i
      · simp [p', h1, h2, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega,
          show (m : ℕ) < k by omega]
      · by_cases h3 : (m : ℕ) = i
        · simp [p', h3, show ¬ i < j by omega]
        · simp [h1, h2, show ¬ (m : ℕ) < i + 1 by omega]
  -- so the piece's own vertex is below the plane
  have hP : ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun m => if (m : ℕ) < i + 1 then p' m else false) x ≤ α := by
    rw [hpre]
    refine le_trans (Interval.corner_sum_mono hb0' fun m hm => ?_) hPk
    by_cases h1 : (m : ℕ) < j
    · simpa [h1] using hm
    · simp only [h1, if_false, decide_eq_true_eq] at hm ⊢; omega
  obtain ⟨-, hjk', hkn', hPk', hnext'⟩ :=
    Interval.exploreBN_step_spec b α (i + 1) p' (by omega) hb0' hP
  simp only at hjk' hkn' hPk' hnext'
  set k' := max (i + 1) (Nat.findGreatest (fun k => ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
    (fun m : Fin n => if (m : ℕ) < i + 1 then p' m else decide ((m : ℕ) < k)) x ≤ α) n)
    with hk'def
  set u : Fin n → Bool := fun m => if (m : ℕ) < i + 1 then p' m else decide ((m : ℕ) < k')
    with hudef
  -- the piece's visited vertex `u` lies in it and below the plane
  refine ⟨u, fun m hm => by simp [u, hm], hPk', ?_⟩
  by_cases hk' : k' < n
  · -- the piece stops short of `n`: the next coordinate is raisable
    refine ⟨⟨k', hk'⟩, by simp [u, show ¬ k' < i + 1 by omega], ?_⟩
    have hraise : (fun m : Fin n => if (m : ℕ) < i + 1 then p' m else decide ((m : ℕ) < k' + 1))
        = Function.update u ⟨k', hk'⟩ true := by
      funext m
      by_cases hm : m = ⟨k', hk'⟩
      · subst hm; simp [u, show ¬ k' < i + 1 by omega]
      · rw [Function.update_of_ne hm]
        have : (m : ℕ) ≠ k' := fun h => hm (Fin.ext h)
        by_cases h1 : (m : ℕ) < i + 1
        · simp [u, h1]
        · simp only [u, h1, if_false]
          by_cases h2 : (m : ℕ) < k' <;> simp [h2] <;> omega
    rw [← Interval.corner_sum_update (by simp [u, show ¬ k' < i + 1 by omega]), ← hraise]
    exact not_le.mp (hnext' hk')
  · -- the piece raises all the rest: its coordinate `i` is raisable, past `lab (k + 1)`
    have hin : i < n := by omega
    refine ⟨⟨i, hin⟩, by simp [u, p'], ?_⟩
    rw [← Interval.corner_sum_update (by simp [u, p'])]
    refine lt_of_lt_of_le hnext (Interval.corner_sum_mono hb0' fun m hm => ?_)
    by_cases hmi : m = ⟨i, hin⟩
    · rw [hmi, Function.update_self]
    rw [Function.update_of_ne hmi]
    have hmi' : (m : ℕ) ≠ i := fun h => hmi (Fin.ext h)
    by_cases h1 : (m : ℕ) < j
    · simp only [h1, if_true] at hm
      simp [u, p', show (m : ℕ) < i + 1 by omega, hmi', h1, hm]
    · simp only [h1, if_false, decide_eq_true_eq] at hm
      by_cases h2 : (m : ℕ) < i
      · simp [u, p', show (m : ℕ) < i + 1 by omega, hmi', h1, show (m : ℕ) < k by omega]
      · simp [u, show ¬ (m : ℕ) < i + 1 by omega, show (m : ℕ) < k' by omega]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
