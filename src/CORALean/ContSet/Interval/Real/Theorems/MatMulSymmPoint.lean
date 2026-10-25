module

public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.Interval.Real.Operations.MatMul

@[expose] public section

/-!
# A symmetric interval matrix times a point matrix, in closed form

[1, Lemma 2]. `Interval.matMul` bounds a general interval-times-interval product through four corner
bounds per summand; when the left factor is symmetric (`S.inf = -S.sup`) and the right one a single
matrix rather than an interval, those corners collapse entrywise to `|M|` scaled by `S.sup` — the
`ST = ⟨-Ŝ|T|, Ŝ|T|⟩` half of [1, Lemma 2]'s (6). Proved at full matrix generality, one column of `M`
at a time, needing no regularity of `M`, only that `M` is a point. The bound is stated entrywise, as
CORA's row/column sum is. `S.IsNonempty` stands in for "`S = [-S̄, S̄]` is a genuine interval":
crossed bounds would make `S.sup` negative somewhere.

## Inputs
* `S` – symmetric interval matrix
* `M` – point matrix

## Hypotheses
* `hSne` – `S` nonempty
* `hSsymm` – lower bound is the negated upper bound

## Conclusion
* the product with a point matrix is the symmetric box of absolute sums

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The two corners a symmetric term `[-s, s] * t` reaches. -/
theorem aux_corners_symm_mul (s t : ℝ) (hs : 0 ≤ s) : -- --- CONCL ---
    min (-(s * t)) (s * t) = -(s * |t|) ∧ max (-(s * t)) (s * t) = s * |t| := by -- --- PROOF ---
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact ⟨min_eq_left (by nlinarith), max_eq_right (by nlinarith)⟩
  · rw [abs_of_nonpos ht]
    exact ⟨by rw [min_eq_right (by nlinarith)]; ring, by rw [max_eq_left (by nlinarith)]; ring⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matMul_symm_point {S : Interval (Mat ℝ m n)} (hSne : S.IsNonempty)
    (hSsymm : S.inf = -S.sup) (M : Mat ℝ n p) : -- --- CONCL ---
    Interval.matMul S (Interval.point M) = ⟨fun i j => -(∑ k, S.sup i k * |M k j|),
      fun i j => ∑ k, S.sup i k * |M k j|⟩ := by -- --- PROOF ---
  have hSik : ∀ i k, S.inf i k = -(S.sup i k) := fun i k => by
    simpa using congrFun (congrFun hSsymm i) k
  have hSnn : ∀ i k, 0 ≤ S.sup i k := fun i k => by
    have h := hSne (i, k)
    simp only [Entrywise.entry_mat] at h
    linarith [hSik i k ▸ h]
  -- unfold `matMul` and `point` so `congr` can match the two fields in turn
  show (⟨fun i j => ∑ k, Interval.mulLo (S.inf i k) (S.sup i k) (M k j) (M k j),
        fun i j => ∑ k, Interval.mulHi (S.inf i k) (S.sup i k) (M k j) (M k j)⟩
        : Interval (Mat ℝ m p))
      = ⟨fun i j => -(∑ k, S.sup i k * |M k j|), fun i j => ∑ k, S.sup i k * |M k j|⟩
  congr 1
  · funext i j
    have hterm : ∀ k, Interval.mulLo (S.inf i k) (S.sup i k) (M k j) (M k j)
        = -(S.sup i k * |M k j|) := fun k => by
      simp only [Interval.mulLo, hSik i k, neg_mul, min_self]
      exact (aux_corners_symm_mul (S.sup i k) (M k j) (hSnn i k)).1
    simp only [hterm, Finset.sum_neg_distrib]
  · funext i j
    have hterm : ∀ k, Interval.mulHi (S.inf i k) (S.sup i k) (M k j) (M k j)
        = S.sup i k * |M k j| := fun k => by
      simp only [Interval.mulHi, hSik i k, neg_mul, max_self]
      exact (aux_corners_symm_mul (S.sup i k) (M k j) (hSnn i k)).2
    simp only [hterm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
