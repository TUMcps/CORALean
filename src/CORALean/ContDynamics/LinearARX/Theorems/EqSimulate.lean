import CORALean.ContDynamics.LinearARX.Operations.Simulate

/-!
# A run is determined by its first window and its inputs

Any output sequence satisfying the ARMAX recursion from `p` on, with first window `y₀`, is
`simulate y₀ u`. By strong induction: the first `p` outputs are read off `y₀`, and every
later one is the recursion over earlier ones.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.eq_simulate (sys : LinearARX 𝕋 dy du p) {y₀ : Vec ℝ (p * dy)}
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (h₀ : LinearARX.stack p y 0 = y₀)
    (hy : ∀ k, p ≤ k →
      y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
        + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)) (k : ℕ) :
    y k = sys.simulate y₀ u k := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < p
    · rw [LinearARX.simulate, dif_pos hk]
      funext b
      rw [← h₀]
      show y k b = y (0 + (finProdFinEquiv.symm (finProdFinEquiv (⟨k, hk⟩, b))).1)
        (finProdFinEquiv.symm (finProdFinEquiv (⟨k, hk⟩, b))).2
      rw [Equiv.symm_apply_apply, zero_add]
    · rw [LinearARX.simulate, dif_neg hk, hy k (not_lt.mp hk)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (k - (i + 1)) (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
