module

public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Operations.SoftmaxRawLower
public import CORALean.NN.Layers.Theorems.Real.RawLeSoftmax
public import CORALean.NN.Layers.Theorems.SumEraseLeSumOffUp
public import CORALean.NN.Layers.Theorems.SoftmaxRawLowerLe

@[expose] public section

/-!
# What the normalization buys

The outputs sum to one, so each is what the others leave over. Stated for arbitrary raw bounds
because a machine scalar passes `0` below, where the normalization is not a tightening but the
only lower bound available.

## Inputs
* `x` – input vector
* `rl` – raw lower bounds of the softmax
* `ru` – raw upper bounds of the softmax
* `i` – output coordinate

## Hypotheses
* `hl` – the raw lower bounds hold
* `hu` – the raw upper bounds hold

## Conclusion
* the softmax lies within the bounds tightened by the normalization
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The constraint the enclosure is built to keep, and a fact a specification may use directly. -/
theorem aux_softmax_sum_eq_one (x : Vec ℝ n) (i : Fin n) : ∑ j, softmax x j = 1 := by
  show ∑ j, Real.exp (x j) / (∑ k, Real.exp (x k)) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (exp_sum_pos x i))


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_mem_tightened (x rl ru : Vec ℝ n)
    (hl : ∀ i, rl i ≤ softmax x i) (hu : ∀ i, softmax x i ≤ ru i) (i : Fin n) : -- --- CONCL ---
    max (rl i) (1 - ∑ j ∈ Finset.univ.erase i, ru j) ≤ softmax x i ∧
      softmax x i ≤ min (ru i) (1 - ∑ j ∈ Finset.univ.erase i, rl j) := by -- --- PROOF ---
  have hsplit : softmax x i + ∑ j ∈ Finset.univ.erase i, softmax x j = 1 := by
    rw [Finset.add_sum_erase Finset.univ (softmax x) (Finset.mem_univ i)]
    exact aux_softmax_sum_eq_one x i
  have hru : ∑ j ∈ Finset.univ.erase i, softmax x j ≤ ∑ j ∈ Finset.univ.erase i, ru j :=
    Finset.sum_le_sum fun j _ => hu j
  have hrl : ∑ j ∈ Finset.univ.erase i, rl j ≤ ∑ j ∈ Finset.univ.erase i, softmax x j :=
    Finset.sum_le_sum fun j _ => hl j
  exact ⟨max_le (hl i) (by linarith), le_min (hu i) (by linarith)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
