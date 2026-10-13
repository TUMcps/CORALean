module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScalarTermLe
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A series dominated by the exponential's tail sums to no more than it

`scalar_term_le` termwise against a geometric series, whose sum is the closed
form `MatExp.expRemainderBound` is written in, and the majorant carries the
summability of whatever is dominated, so a caller supplies neither.

Stated at bare reals rather than at `‖x‖`, and over a dominated sequence rather
than the tail itself: no matrix appears, so the matrix norm instances every
caller makes local stay out of the elaboration, and a caller that has bounded
its own terms is done. The scale `s` is what an integrated series carries — one
factor of the step in front of each order.

The side condition is the one every enclosure here carries; without it the
geometric series diverges and there is nothing to sum.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Anything under `s` times the orders past `η` sums to under `s` times the
closed form `expRemainderBound` names. -/
theorem tsum_le_expTail {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (η : ℕ)
    (hε : c / ((η : ℝ) + 2) < 1) {a : ℕ → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha : ∀ i, a i ≤ s * ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * c ^ (i + (η + 1)))) :
    ∑' i : ℕ, a i ≤ s * ((c ^ (η + 1) / Nat.factorial (η + 1))
      * (1 - c / ((η : ℝ) + 2))⁻¹) := by -- --- PROOF ---
  have hε0 : (0:ℝ) ≤ c / ((η : ℝ) + 2) := div_nonneg hc (by positivity)
  have hgeo : Summable (fun i : ℕ => (c / ((η : ℝ) + 2)) ^ i) :=
    summable_geometric_of_lt_one hε0 hε
  have hmaj : Summable (fun i : ℕ =>
      s * (c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (c / ((η : ℝ) + 2)) ^ i) :=
    hgeo.mul_left _
  -- every term under the geometric majorant, which is where summability comes from
  have hterm : ∀ i : ℕ, a i
      ≤ s * (c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (c / ((η : ℝ) + 2)) ^ i := by
    intro i
    refine (ha i).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (scalar_term_le hc η i) hs
  have hsa : Summable a := Summable.of_nonneg_of_le ha0 hterm hmaj
  -- `gcongr` rather than `Summable.tsum_le_tsum`, which spends a minute on the filter
  have hle : ∑' i : ℕ, a i
      ≤ ∑' i : ℕ, s * (c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ))
          * (c / ((η : ℝ) + 2)) ^ i := by
    gcongr ∑' i, ?_ with i
    exact hterm i
  rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε] at hle
  rw [← mul_assoc]
  exact hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
