module

public import CORALean.Global.SindyThreshold

@[expose] public section

/-!
# What a fixed point of sequential thresholded least squares is

For a fixed point `Ξ` of a pass of [1, Alg. 1], the paper's `Code 1`: every coefficient is either
zero, if below `λ` in magnitude, or what the regression onto the surviving terms of its column
gives. So every nonzero coefficient is at least `λ`, and if the regression returns a solution of
its normal equations, `Θᵀ (Ẋ - Θ Ξ)` vanishes at every surviving term: a least-squares fit onto
its support, but not necessarily the best one among all supports. If the data come from a sparse
`Ξ*` whose nonzero coefficients are all at least `λ`, and the regression returns `Ξ*` whenever
given terms that include the support of the column (as an exact fit onto linearly independent
terms does), `Code 1` returns `Ξ*` after any number of passes.

## Inputs
* `lam` – threshold
* `solve` – regression onto a set of terms
* `Ξ` – coefficient matrix
* `j` – term index
* `c` – column index

## Hypotheses
* `hfix` – the matrix is unchanged by a pass

## Conclusion
* each coefficient is zero below the threshold, else the regression onto the surviving terms

## References

* [1] S. L. Brunton, J. L. Proctor and J. N. Kutz. "Discovering governing equations from data by
      sparse identification of nonlinear dynamical systems". Proceedings of the National
      Academy of Sciences, 113(15):3932-3937, 2016 (arXiv:1509.03580).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m p n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A fixed point is zero where it is below `λ` and the regression onto the survivors where not. -/
theorem sindy_fixed_spec (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ) (Ξ : Mat ℝ p n)
    (hfix : sindyStep lam solve Ξ = Ξ) (j : Fin p) (c : Fin n) : -- --- CONCL ---
    (|Ξ j c| < lam → Ξ j c = 0) ∧
      (lam ≤ |Ξ j c| →
        Ξ j c = solve c (Finset.univ.filter fun i => lam ≤ |Ξ i c|) j) := by -- --- PROOF ---
  have h := congrFun (congrFun hfix j) c
  simp only [sindyStep, Matrix.of_apply] at h
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [← h]; simp [hs]
  · have hns : ¬ |Ξ j c| < lam := not_lt.mpr hs
    rw [← h]
    simp [hns]

/-- If the regression solves its normal equations, a fixed point does at every surviving term. -/
theorem sindy_fixed_normalEq (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (Θ : Mat ℝ m p) (dX : Mat ℝ m n)
    (hsolve : ∀ c S, ∀ i ∈ S,
      ∑ t, Θ t i * (dX t c - ∑ j ∈ S, Θ t j * solve c S j) = 0)
    (Ξ : Mat ℝ p n) (hfix : sindyStep lam solve Ξ = Ξ) (c : Fin n) (i : Fin p)
    (hi : lam ≤ |Ξ i c|) : -- --- CONCL ---
    ∑ t, Θ t i * (dX t c - ∑ j, Θ t j * Ξ j c) = 0 := by -- --- PROOF ---
  set S := Finset.univ.filter fun i => lam ≤ |Ξ i c| with hS
  have hsum : ∀ t, ∑ j, Θ t j * Ξ j c = ∑ j ∈ S, Θ t j * solve c S j := fun t => by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [((sindy_fixed_spec lam solve Ξ hfix j c).2 (Finset.mem_filter.mp hj).2)]
    · intro j _ hj
      have : |Ξ j c| < lam := by
        by_contra hge
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
      rw [(sindy_fixed_spec lam solve Ξ hfix j c).1 this, mul_zero]
  simp only [hsum]
  exact hsolve c S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- Exact data of a sparse `Ξ*`: `Code 1` returns `Ξ*` after every number of passes. -/
theorem sindy_recovers (lam : ℝ) (solve : Fin n → Finset (Fin p) → Fin p → ℝ)
    (Ξs : Mat ℝ p n) (hbig : ∀ j c, Ξs j c ≠ 0 → lam ≤ |Ξs j c|)
    (hsolve : ∀ c S, (∀ j, Ξs j c ≠ 0 → j ∈ S) → ∀ j ∈ S, solve c S j = Ξs j c) (K : ℕ) :
    sindy lam solve K = Ξs := by -- --- PROOF ---
  have h0 : (Matrix.of fun j c => solve c Finset.univ j : Mat ℝ p n) = Ξs := by
    ext j c
    exact hsolve c Finset.univ (fun j _ => Finset.mem_univ j) j (Finset.mem_univ j)
  have hfix : sindyStep lam solve Ξs = Ξs := by
    ext j c
    simp only [sindyStep, Matrix.of_apply]
    by_cases hs : |Ξs j c| < lam
    · have h0' : Ξs j c = 0 := by
        by_contra hne
        exact absurd (hbig j c hne) (not_le.mpr hs)
      simp only [hs, if_true]
      exact h0'.symm
    · simp only [hs, if_false]
      refine hsolve c _ (fun i hi => ?_) j ?_
      · simpa using hbig i c hi
      · simpa using not_lt.mp hs
  show (sindyStep lam solve)^[K] (Matrix.of fun j c => solve c Finset.univ j) = Ξs
  rw [h0]
  exact Function.iterate_fixed hfix K

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
