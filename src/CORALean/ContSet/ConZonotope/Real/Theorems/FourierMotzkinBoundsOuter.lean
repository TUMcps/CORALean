module

public import CORALean.ContSet.ConZonotope.Real.Operations.FourierMotzkinBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The Fourier-Motzkin bounds enclose the constrained hypercube

[1, Prop. 3]: `P = ⟨C, d⟩_H ∩ [β̲₀, β̄₀] ⊆ [β̲, β̄]` for `ConZonotope.fourierMotzkinBounds`. For
`β ∈ P` and a row `i` with `C(i,j) ≠ 0`, `C(i,j) β(j) ≤ d(i) - C(i,·) Σ_{∖{j}} β`, and
`C(i,·) Σ_{∖{j}} β ≥ C⁺(i,·) Σ_{∖{j}} β̲₀ + C⁻(i,·) Σ_{∖{j}} β̄₀` on the box; dividing by
`C(i,j)` bounds `β(j)` below where it is negative and above where it is positive. With `C⁻` the
entries `≤ 0`, `½(C - |C|)`, as the proof's last step reads it.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `B` – initial bounds `[β̲₀, β̄₀]`

## Hypotheses
* none

## Conclusion
* the constrained hypercube lies in the bounds

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `M(i,·) Σ_{∖{j}} v` drops the `j`-th entry of `v`. -/
private theorem aux_excl_mulVec (M : Mat ℝ p q) (j : Fin q) (v : Vec ℝ q)
    (i : Fin p) : -- --- CONCL ---
    ((M * (1 - Matrix.single j j (1 : ℝ) : Mat ℝ q q)) *ᵥ v) i =
      ∑ k, M i k * (if k = j then 0 else v k) := by -- --- PROOF ---
  rw [← mulVec_mulVec, sub_mulVec, one_mulVec, single_mulVec]
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

/-- The rest of row `i` over the box: `C⁺ Σ_{∖{j}} β̲₀ + C⁻ Σ_{∖{j}} β̄₀ ≤ C(i,·) Σ_{∖{j}} β`. -/
private theorem aux_rest_le (C : Mat ℝ p q) (B : Interval (Vec ℝ q)) (β : Vec ℝ q)
    (hB : ∀ k, B.inf k ≤ β k ∧ β k ≤ B.sup k) (i : Fin p) (j : Fin q) : -- --- CONCL ---
    ∑ k, (C i k + |C i k|) / 2 * (if k = j then 0 else B.inf k) +
        ∑ k, (C i k - |C i k|) / 2 * (if k = j then 0 else B.sup k) ≤
      ∑ k, C i k * (if k = j then 0 else β k) := by -- --- PROOF ---
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = j
  · simp [hk]
  · simp only [hk, if_false]
    -- `C⁺ ≥ 0` meets the lower bound, `C⁻ ≤ 0` the upper one
    have hp : 0 ≤ (C i k + |C i k|) / 2 := by linarith [neg_abs_le (C i k)]
    have hm : (C i k - |C i k|) / 2 ≤ 0 := by linarith [le_abs_self (C i k)]
    have h1 := mul_le_mul_of_nonneg_left (hB k).1 hp
    have h2 := mul_le_mul_of_nonpos_left (hB k).2 hm
    nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: the bounds enclose the constrained hypercube. -/
theorem ConZonotope.fourierMotzkinBounds_outer (C : Mat ℝ p q) (d : Vec ℝ p)
    (B : Interval (Vec ℝ q)) : -- --- CONCL ---
    (HPolytope.ineqs C d).construct ∩ B.construct ⊆
      (ConZonotope.fourierMotzkinBounds C d B).construct := by -- --- PROOF ---
  rintro β ⟨hP, hB⟩ j
  have hB' : ∀ k, B.inf k ≤ β k ∧ β k ≤ B.sup k := fun k => hB k
  -- row `i` isolates `β(j)`: `C(i,j) β(j) ≤ d(i) - C⁺ Σ β̲₀ - C⁻ Σ β̄₀`
  have hrow : ∀ i, C i j * β j ≤ d i -
      ∑ k, (C i k + |C i k|) / 2 * (if k = j then 0 else B.inf k) -
      ∑ k, (C i k - |C i k|) / 2 * (if k = j then 0 else B.sup k) := by
    intro i
    have hPi := (HPolytope.mem_ineqs_iff).1 hP i
    have hsplit : (C *ᵥ β) i = C i j * β j + ∑ k, C i k * (if k = j then 0 else β k) := by
      simp only [mulVec, dotProduct, mul_ite, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← Finset.add_sum_erase _ _
        (Finset.mem_univ j), Finset.filter_ne' Finset.univ j]
    linarith [aux_rest_le C B β hB' i j]
  simp only [ConZonotope.fourierMotzkinBounds, aux_excl_mulVec]
  refine ⟨(Finset.fold_max_le (β j)).2 ⟨(hB' j).1, fun i hi => ?_⟩,
    (Finset.le_fold_min (β j)).2 ⟨(hB' j).2, fun i hi => ?_⟩⟩
  · -- a negative `C(i,j)` bounds `β(j)` from below
    have hneg := (Finset.mem_filter.1 hi).2
    rw [div_le_iff_of_neg hneg]
    linarith [hrow i]
  · -- a positive `C(i,j)` bounds it from above
    have hpos := (Finset.mem_filter.1 hi).2
    rw [le_div_iff₀ hpos]
    linarith [hrow i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
