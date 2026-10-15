module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ImageEnclosureCostLe
public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetDepth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetMaxWidth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetNeurons
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ForwardCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic

@[expose] public section

/-!
# `SetBasedNet.forwardCost_le`

[1, Prop. 16], the running time: `O(n_max² q κ)`, `n_max` over every width the input's
included and `q` the generator count, at most `(cNeuron + 10) N² Q κ`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 16], the running time: `O(n_max² q κ)`, `n_max` over every width the input's
included and `q` the generator count, at most `(cNeuron + 10) N² Q κ`. -/
theorem SetBasedNet.forwardCost_le (cNeuron : Cost) {N Q : ℕ} (hN : 1 ≤ N) {n k : ℕ}
    (net : SetBasedNet n k) :
    ∀ h, 1 ≤ h → net.maxWidth ≤ N → h + net.neurons ≤ Q →
      (net.forwardCost cNeuron h).ops ≤
        (cNeuron.ops + 10) * (N * N * Q) * net.depth := by -- --- PROOF ---
  induction net with
  | output => intro _ _ _ _; simp [SetBasedNet.forwardCost]
  | @linear n m k W b tail ih =>
      intro h hh hw hq
      -- `max n (tail's widths) ≤ N`, and the tail adds `m` fewer neurons
      have hw' : max n tail.maxWidth ≤ N := hw
      have hq' : h + (m + tail.neurons) ≤ Q := hq
      have htail := ih h hh (le_of_max_le_right hw') (by omega)
      have hmN : m ≤ N := by
        cases tail with
        | output => exact le_of_max_le_right hw'
        | linear => exact (le_max_left _ _).trans (le_of_max_le_right hw')
        | nonlinear => exact (le_max_left _ _).trans (le_of_max_le_right hw')
      have hp := SetBasedNet.mul_mul_le_of_le hmN (le_of_max_le_left hw') (by omega : h ≤ Q)
      have hp1 : m * 1 * 1 ≤ N * N * Q := SetBasedNet.mul_mul_le_of_le hmN hN (by omega)
      have hmn : m * n ≤ m * n * h := Nat.le_mul_of_pos_right _ hh
      show (Zonotope.mtimesCost m n h + Zonotope.plusCost m +
          tail.forwardCost cNeuron h).ops ≤ (cNeuron.ops + 10) * (N * N * Q) * (tail.depth + 1)
      simp only [Zonotope.mtimesCost, Zonotope.plusCost, Cost.matVec, Cost.ops_add,
        Cost.ops_smul] at htail ⊢
      -- the layer at `5 N² Q`, the rest the tail's
      have e1 : (h + 1) * (2 * (m * n)) = 2 * (m * n * h) + 2 * (m * n) := by ring
      have e2 : m * 1 * 1 = m := by ring
      have hsplit : (cNeuron.ops + 10) * (N * N * Q) * (tail.depth + 1) =
          (cNeuron.ops + 10) * (N * N * Q) * tail.depth + cNeuron.ops * (N * N * Q) +
            10 * (N * N * Q) := by ring
      rw [hsplit]
      omega
  | @nonlinear n k me eLo eUp tail ih =>
      intro h hh hw hq
      -- the layer at `h` generators, the tail at `h + n`
      have hw' : max n tail.maxWidth ≤ N := hw
      have hq' : h + (n + tail.neurons) ≤ Q := hq
      have htail := ih (h + n) (by omega) (le_of_max_le_right hw') (by omega)
      have hnN : n ≤ N := le_of_max_le_left hw'
      have hlay : (Zonotope.imageEnclosureCost n h cNeuron).ops ≤
          (cNeuron.ops + 10) * (N * N * Q) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Zonotope.plusCost,
            Cost.matVec]
        · exact (Zonotope.imageEnclosureCost_le n h cNeuron hn hh).trans
            (Nat.mul_le_mul_left _ (SetBasedNet.mul_mul_le_of_le hnN hnN (by omega)))
      show (Zonotope.imageEnclosureCost n h cNeuron + tail.forwardCost cNeuron (h + n)).ops ≤
        (cNeuron.ops + 10) * (N * N * Q) * (tail.depth + 1)
      rw [Cost.ops_add, Nat.mul_succ]
      omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
