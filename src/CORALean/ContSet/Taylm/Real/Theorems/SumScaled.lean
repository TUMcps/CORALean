module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.Basic

@[expose] public section

/-!
# `Taylm.sum` keeps the scaling

Models scaled by `C i` at a common order `N` sum to one whose weight is at most `Σ C i` and whose
remainder is at most `(Σ C i)·hᴺ⁺¹`. The empty sum has order `0`, so the result's order is only
at most `N`, which is the direction [1, Thm. 1] can use.

## Inputs
* `m` – number of models
* `T` – family of models
* `h` – domain radius
* `C` – scaling constants
* `N` – expansion order

## Hypotheses
* `hN` – each model has the expansion order
* `hT` – each model is scaled by its constant

## Conclusion
* the sum's weight and remainders are bounded by the summed constants

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sum_scaled {m : ℕ} {T : Fin m → Taylm n} {h : ℝ} {C : Fin m → ℝ} {N : ℕ}
    (hN : ∀ i, (T i).maxOrder = N) (hT : ∀ i, (T i).Scaled h (C i)) : -- --- CONCL ---
    Taylm.weight (Taylm.sum T).terms h ≤ ∑ i, C i ∧
      |(Taylm.sum T).rem.inf| ≤ (∑ i, C i) * h ^ (N + 1) ∧
      |(Taylm.sum T).rem.sup| ≤ (∑ i, C i) * h ^ (N + 1) ∧
      (Taylm.sum T).maxOrder ≤ N := by -- --- PROOF ---
  induction m with
  | zero => simp [Taylm.sum, Taylm.weight]
  | succ m ih =>
    obtain ⟨w, i, s, o⟩ := ih (T := fun i => T i.succ) (C := fun i => C i.succ)
      (fun i => hN _) (fun i => hT _)
    obtain ⟨w₀, i₀, s₀⟩ := hT 0
    rw [hN 0] at i₀ s₀
    simp only [Taylm.sum, Taylm.plus, Taylm.weight_append, Fin.sum_univ_succ, add_mul]
    exact ⟨add_le_add w₀ w, le_trans (abs_add_le _ _) (add_le_add i₀ i),
      le_trans (abs_add_le _ _) (add_le_add s₀ s), max_le (hN 0).le o⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
