module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section

/-!
# The peak of a disturbance is at most the worst case of its set

[1, Remark 1], corrected: every run with `d_k ∈ ⟨0, H_d⟩` has
`sup_k ‖d_k‖ ≤ max_{b ∈ B} ‖H_d b‖`; the paper prints `=` (its Eq. 3), which fails
(`LinearSysDT.peakDisturbance_counterexample`). Each `‖d_k‖ = ‖H_d b_k‖` is a value of the maximum,
bounded since the box is.

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {nd m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.peakDisturbance_le (Hd : Mat ℝ nd m) (d : ℕ → Vec ℝ nd) (ℓ : ℝ)
    (hℓ : ∀ b : Vec ℝ m, (∀ i, |b i| ≤ 1) → Real.sqrt ((Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b)) ≤ ℓ)
    (hd : ∀ k, ∃ b : Vec ℝ m, (∀ i, |b i| ≤ 1) ∧ d k = Hd *ᵥ b) : -- --- CONCL ---
    (⨆ k, Real.sqrt (d k ⬝ᵥ d k)) ≤
      sSup ((fun b : Vec ℝ m => Real.sqrt ((Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b))) ''
        {b | ∀ i, |b i| ≤ 1}) := by -- --- PROOF ---
  have hbdd : BddAbove ((fun b : Vec ℝ m => Real.sqrt ((Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b))) ''
      {b | ∀ i, |b i| ≤ 1}) := ⟨ℓ, by rintro _ ⟨b, hb, rfl⟩; exact hℓ b hb⟩
  -- each `‖d_k‖` is a value of the maximum
  refine ciSup_le fun k => ?_
  obtain ⟨b, hb, hk⟩ := hd k
  exact le_csSup hbdd ⟨b, hb, by rw [hk]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
