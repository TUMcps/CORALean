module

public import CORALean.ContSet.Zonotope.Real.Theorems.ScanEdgeSpec

@[expose] public section

/-!
# The loops of [1, Alg. 3] record the extremes over all the edges they pass

A loop `for j from 1 to r` that moves `P` by `d j` and scans the edge `[P; P + d j]` ends at
`P₀ + ∑ d`. Its `m` is below every `y` at which an edge meets `L_γ` and its `M` above, and each is
the starting value or such a `y`: an induction over the loop, peeling the first edge, on the edge
update `scanEdge_spec`. `step` is the move, `P ± 2 g_j`, given with the vector it adds.

## Inputs
* `n` – step count
* `γ` – abscissa of the vertical line
* `d` – edge vectors
* `step` – position update
* `P₀` – starting point
* `mM₀` – starting interval
* `s` – final state

## Hypotheses
* `hstep` – steps add the edge vectors
* `hs` – `s` is the fold result

## Conclusion
* the fold ends at the summed point with the interval covering all edges

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.scan_fold {n : ℕ} (γ : ℝ) (d : Fin n → Vec ℝ 2)
    (step : Vec ℝ 2 → Fin n → Vec ℝ 2) (hstep : ∀ P j, step P j = P + d j) (P₀ : Vec ℝ 2)
    (mM₀ : Interval EReal) (s : Vec ℝ 2 × Interval EReal)
    (hs : Fin.foldl n (fun s j => (step s.1 j, Zonotope.scanEdge γ s.1 (step s.1 j) s.2))
      (P₀, mM₀) = s) : -- --- CONCL ---
    s.1 = P₀ + ∑ i, d i ∧ s.2.inf ≤ mM₀.inf ∧ mM₀.sup ≤ s.2.sup ∧
    (∀ (k : Fin n) (y : ℝ), (![γ, y] : Vec ℝ 2) ∈ segment ℝ
        (P₀ + ∑ i, if i < k then d i else 0) (P₀ + (∑ i, if i < k then d i else 0) + d k) →
      s.2.inf ≤ y ∧ (y : EReal) ≤ s.2.sup) ∧
    (s.2.inf = mM₀.inf ∨ ∃ (k : Fin n) (y : ℝ), (![γ, y] : Vec ℝ 2) ∈ segment ℝ
        (P₀ + ∑ i, if i < k then d i else 0) (P₀ + (∑ i, if i < k then d i else 0) + d k) ∧
      s.2.inf = y) ∧
    (s.2.sup = mM₀.sup ∨ ∃ (k : Fin n) (y : ℝ), (![γ, y] : Vec ℝ 2) ∈ segment ℝ
        (P₀ + ∑ i, if i < k then d i else 0) (P₀ + (∑ i, if i < k then d i else 0) + d k) ∧
      s.2.sup = y) := by -- --- PROOF ---
  induction n generalizing P₀ mM₀ s with
  | zero =>
    rw [Fin.foldl_zero] at hs
    subst hs
    exact ⟨by simp, le_rfl, le_rfl, fun k => k.elim0, Or.inl rfl, Or.inl rfl⟩
  | succ n ih =>
    rw [Fin.foldl_succ] at hs
    -- the first edge, then the loop over the others
    obtain ⟨hm1, hM1, hedge, hmh, hMh⟩ := Zonotope.scanEdge_spec γ P₀ (step P₀ 0) mM₀
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ := ih (fun i => d i.succ) (fun P j => step P j.succ)
      (fun P j => hstep P j.succ) (step P₀ 0) (Zonotope.scanEdge γ P₀ (step P₀ 0) mM₀)
      s (by simpa using hs)
    -- the prefix sums peel off the first generator
    have hpre : ∀ k : Fin n, (∑ i : Fin (n + 1), if i < k.succ then d i else 0)
        = d 0 + ∑ i : Fin n, if i < k then d i.succ else 0 := fun k => by
      rw [Fin.sum_univ_succ]
      simp [Fin.succ_pos, Fin.succ_lt_succ_iff]
    -- the end point, the bounds, and the attained values
    refine ⟨?_, ih2.trans hm1, hM1.trans ih3, ?_, ?_, ?_⟩
    · rw [ih1, Fin.sum_univ_succ, hstep]; abel
    · intro k y hy
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · simp only [Fin.not_lt_zero, if_false, Finset.sum_const_zero, add_zero] at hy
        obtain ⟨h1, h2⟩ := hedge y (by simpa [hstep] using hy)
        exact ⟨ih2.trans h1, h2.trans ih3⟩
      · rw [hpre k'] at hy
        refine ih4 k' y ?_
        rw [hstep] at *
        convert hy using 2 <;> abel
    -- `m` is attained by the first edge, a later one, or is the start
    · rcases ih5 with h | ⟨k, y, hy, h⟩
      · rcases hmh with h' | ⟨y, hy, h'⟩
        · exact Or.inl (h.trans h')
        · refine Or.inr ⟨0, y, ?_, h.trans h'⟩
          simpa [hstep] using hy
      · refine Or.inr ⟨k.succ, y, ?_, h⟩
        rw [hpre k]
        rw [hstep] at hy
        convert hy using 2 <;> abel
    -- and `M`
    · rcases ih6 with h | ⟨k, y, hy, h⟩
      · rcases hMh with h' | ⟨y, hy, h'⟩
        · exact Or.inl (h.trans h')
        · refine Or.inr ⟨0, y, ?_, h.trans h'⟩
          simpa [hstep] using hy
      · refine Or.inr ⟨k.succ, y, ?_, h⟩
        rw [hpre k]
        rw [hstep] at hy
        convert hy using 2 <;> abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
