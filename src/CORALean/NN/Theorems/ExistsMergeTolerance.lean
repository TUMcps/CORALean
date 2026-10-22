module

public import CORALean.NN.Theorems.MergeErrorWidthLeRow
public import CORALean.NN.Operations.MergeRowWeight
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# A tolerance meeting any error budget

Not [1]'s Alg. 1, which bisects for a `δ` hitting a *reduction rate* `ρ` — a target neuron count,
not an error budget — and whose answer owes no proof, as `neuronMerging_sandwich_outer` is sound at
every bucket. This is the budget read the other way: for every `ε` some `δ` meets it at every bucket
and every output, since `mergeError_width_le_row`'s bound is linear in `δ`. The witness `δ := ε / (2
* (1 + ∑ mergeRowWeight))` carries a `+ 1` in its denominator so it stays positive even at `W = 0`,
with no case split and no `Finset.sup'`. Same shape as `exists_polyRelaxation_error_lt` in
`NN/Layers/PolyRangeConvergence.lean`.

## Inputs
* `n` – layer width
* `n₂` – output width
* `Y` – bounds of the layer's neurons
* `W` – weight matrix
* `ε` – error budget

## Hypotheses
* `hY` – the bounds are nonempty
* `hε` – the budget is positive

## Conclusion
* some positive tolerance keeps every bucket's cost within the budget

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- ℝ-only, the weights being exact: a sum of absolute values. -/
theorem aux_mergeRowWeight_nonneg {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) :
    0 ≤ mergeRowWeight W i :=
  Finset.sum_nonneg fun k _ => abs_nonneg (W i k)


/-- A row's share of a budget scaled by the sum of every row's weight, plus one,
never exceeds the budget itself. -/
theorem aux_scaled_le {S w ε : ℝ} (hS : 0 ≤ S) (hw : w ≤ S) (hε : 0 < ε) : -- --- CONCL ---
    w * (2 * (ε / (2 * (1 + S)))) ≤ ε := by -- --- PROOF ---
  have hD : (0:ℝ) < 1 + S := by linarith
  have hDne : (1 + S) ≠ 0 := hD.ne'
  have heq : w * (2 * (ε / (2 * (1 + S)))) = (w / (1 + S)) * ε := by
    field_simp
  rw [heq]
  have hfrac : w / (1 + S) ≤ 1 := (div_le_one hD).mpr (by linarith)
  calc (w / (1 + S)) * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hfrac (le_of_lt hε)
    _ = ε := one_mul ε


-- =======================================  MAIN THEOREM  ======================================= --

/-- For every error budget `ε`, a tolerance `δ` under which every bucket, at
every output, costs no more than `ε` — the cost being linear in `δ`. -/
theorem exists_mergeTolerance {n n₂ : ℕ} (Y : Real.Interval (Vec ℝ n)) (hY : Y.IsNonempty)
    (W : Mat ℝ n₂ n) {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ∃ δ : ℝ, 0 < δ ∧ ∀ (y : ℝ) (i : Fin n₂),
      let EB := Real.Interval.mtimes (W.submatrix id (mergeSplit Y y δ).right)
        ⟨Y.inf ∘ (mergeSplit Y y δ).right, Y.sup ∘ (mergeSplit Y y δ).right⟩
      EB.sup i - EB.inf i ≤ ε := by -- --- PROOF ---
  -- the `1` keeps the denominator positive even if every row weight is `0`
  have hSnonneg : (0:ℝ) ≤ ∑ j, mergeRowWeight W j :=
    Finset.sum_nonneg fun j _ => aux_mergeRowWeight_nonneg W j
  have hD : (0:ℝ) < 2 * (1 + ∑ j, mergeRowWeight W j) := by linarith
  refine ⟨ε / (2 * (1 + ∑ j, mergeRowWeight W j)), div_pos hε hD, fun y i => ?_⟩
  intro EB
  have hδnonneg : (0:ℝ) ≤ ε / (2 * (1 + ∑ j, mergeRowWeight W j)) := le_of_lt (div_pos hε hD)
  have hbound := mergeError_width_le_row Y y
    (ε / (2 * (1 + ∑ j, mergeRowWeight W j))) hδnonneg hY W i
  -- a row's weight is at most the sum over every row, each of them nonnegative
  have hrow_le : mergeRowWeight W i ≤ ∑ j, mergeRowWeight W j :=
    Finset.single_le_sum (fun j _ => aux_mergeRowWeight_nonneg W j) (Finset.mem_univ i)
  exact le_trans hbound (aux_scaled_le hSnonneg hrow_le hε)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
