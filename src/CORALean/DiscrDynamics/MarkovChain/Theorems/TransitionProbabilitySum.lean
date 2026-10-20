module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic
public import CORALean.DiscrDynamics.GridPartition.Theorems.MemIntersectingCellsLe

@[expose] public section

/-!
# The empirical cell frequencies add up to one

`priv_transitionProbability` counts, for each point, the first cell `intersectingCells` names,
which is a cell or the outside; every point is counted once, so the shares of a nonempty set of
points add up to `1`.

## Inputs
* `field` – grid partition
* `pts` – final points

## Hypotheses
* `h` – points nonempty

## Conclusion
* the empirical frequencies add up to one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Counting each point under the first cell it lands in counts every point once. -/
theorem MarkovChain.aux_count_sum (field : GridPartition n) (l : List (Vec ℝ n)) :
    ∑ s : Fin (field.nrOfCells + 1),
      ((l.filter fun x => (field.intersectingCells ⟨x, x⟩).headD 0 = s).length : ℝ) = l.length
        := by -- --- PROOF ---
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    -- the new point adds one to the count of its own cell
    have hle : (field.intersectingCells ⟨a, a⟩).headD 0 ≤ field.nrOfCells := by
      cases hl : field.intersectingCells ⟨a, a⟩ with
      | nil => simp
      | cons b t =>
        have : b ≤ field.nrOfCells :=
          GridPartition.mem_intersectingCells_le _ _ (by rw [hl]; exact List.mem_cons_self)
        simpa using this
    let f : Fin (field.nrOfCells + 1) := ⟨(field.intersectingCells ⟨a, a⟩).headD 0, by omega⟩
    -- the count of cell `x` grows by one exactly when `x` is the cell of `a`
    have hx : ∀ x : Fin (field.nrOfCells + 1),
        ((if decide ((field.intersectingCells ⟨a, a⟩).headD 0 = ↑x) = true then
            a :: List.filter (fun y => decide
              ((field.intersectingCells ⟨y, y⟩).headD 0 = ↑x)) l
          else List.filter (fun y => decide
              ((field.intersectingCells ⟨y, y⟩).headD 0 = ↑x)) l).length : ℝ) =
        ((l.filter fun y => decide ((field.intersectingCells ⟨y, y⟩).headD 0 = ↑x)).length : ℝ) +
          (if f = x then 1 else 0) := by
      intro x
      have hfx : (f = x) ↔ ((field.intersectingCells ⟨a, a⟩).headD 0 = ↑x) := by
        rw [Fin.ext_iff]
      by_cases hc : (field.intersectingCells ⟨a, a⟩).headD 0 = ↑x
      · rw [if_pos (by simpa using hc), if_pos (hfx.mpr hc)]
        simp
      · rw [if_neg (by simpa using hc), if_neg (fun h => hc (hfx.mp h))]
        simp
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib, ih]
    simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- The probabilities of the outside and each cell, from a nonempty set of points, sum to `1`. -/
theorem MarkovChain.transitionProbability_sum (field : GridPartition n) {pts : List (Vec ℝ n)}
    (h : pts ≠ []) : ∑ s, MarkovChain.transitionProbability field pts s = 1 := by -- --- PROOF ---
  unfold MarkovChain.transitionProbability
  rw [← Finset.sum_div]
  have hlen : (0 : ℝ) < pts.length := by exact_mod_cast List.length_pos_iff.mpr h
  rw [div_eq_one_iff_eq hlen.ne']
  exact MarkovChain.aux_count_sum field pts

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
