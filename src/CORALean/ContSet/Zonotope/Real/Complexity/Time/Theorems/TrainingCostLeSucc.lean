module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ImageEnclosureCostLe
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.TrainingCost

@[expose] public section

/-!
# `SetBasedNet.trainingCost_le_succ`

Every iteration, `κ + 1` terms each at most `C N² Q`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A linear layer's forward and backward steps, at most `17 N² Q`. -/
theorem SetBasedNet.aux_linear_le {m n h N Q : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h) (hmN : m ≤ N)
    (hnN : n ≤ N) (hhQ : h ≤ Q) :
    (Zonotope.mtimesCost m n h + Zonotope.plusCost m + Zonotope.mtimesCost n m h +
      (⟨2 * (m * n * (h + 1)) + 2 * (m * n)⟩ : Cost) + (⟨2 * m⟩ : Cost)).ops ≤
        17 * (N * N * Q) := by -- --- PROOF ---
  have hp := SetBasedNet.mul_mul_le_of_le hmN hnN hhQ
  have hmn : m * n ≤ m * n * h := Nat.le_mul_of_pos_right _ hh
  have hm' : m * 1 * 1 ≤ N * N * Q := SetBasedNet.mul_mul_le_of_le hmN hN (hh.trans hhQ)
  simp only [Zonotope.mtimesCost, Zonotope.plusCost, Cost.matVec, Cost.ops_add, Cost.ops_smul]
  have e1 : (h + 1) * (2 * (m * n)) = 2 * (m * n * h) + 2 * (m * n) := by ring
  have e2 : (h + 1) * (2 * (n * m)) = 2 * (m * n * h) + 2 * (m * n) := by ring
  have e3 : 2 * (m * n * (h + 1)) = 2 * (m * n * h) + 2 * (m * n) := by ring
  have e4 : m * 1 * 1 = m := by ring
  omega

/-- A nonlinear layer's forward and backward steps. -/
theorem SetBasedNet.aux_nonlinear_le (cNeuron cBack : Cost) {n h N Q : ℕ} (hN : 1 ≤ N)
    (hh : 1 ≤ h) (hnN : n ≤ N) (hhQ : h ≤ Q) :
    (Zonotope.imageEnclosureCost n h cNeuron + (⟨n * (2 * h + 2) + 10 * (n * (h + 1))⟩ : Cost) +
      (n * (h + 1)) • cBack).ops ≤
        (cNeuron.ops + 10) * (N * N * Q) + 24 * (N * N * Q) +
          2 * (N * N * Q) * cBack.ops := by -- --- PROOF ---
  have hp : n * 1 * h ≤ N * N * Q := SetBasedNet.mul_mul_le_of_le hnN hN hhQ
  have hnh : n ≤ n * h := Nat.le_mul_of_pos_right _ hh
  have hlay : (Zonotope.imageEnclosureCost n h cNeuron).ops ≤
      (cNeuron.ops + 10) * (N * N * Q) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Zonotope.plusCost, Cost.matVec]
    · exact (Zonotope.imageEnclosureCost_le n h cNeuron hn hh).trans
        (Nat.mul_le_mul_left _ (SetBasedNet.mul_mul_le_of_le hnN hnN hhQ))
  have e1 : n * (2 * h + 2) + 10 * (n * (h + 1)) = 12 * (n * h) + 12 * n := by ring
  have e2 : n * 1 * h = n * h := by ring
  have hb2 : n * (h + 1) ≤ 2 * (N * N * Q) := by
    have : n * (h + 1) = n * h + n := by ring
    omega
  have hb3 := Nat.mul_le_mul_right cBack.ops hb2
  simp only [Cost.ops_add, Cost.ops_smul]
  omega

/-- The loss gradient at the output, at most `2 N² Q cGrad`. -/
theorem SetBasedNet.aux_output_le (cGrad : Cost) {n h N Q : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h)
    (hnN : n ≤ N) (hhQ : h ≤ Q) :
    ((n * (h + 1)) • cGrad).ops ≤ 2 * (N * N * Q) * cGrad.ops := by -- --- PROOF ---
  have hp : n * 1 * h ≤ N * N * Q := SetBasedNet.mul_mul_le_of_le hnN hN hhQ
  have hnh : n ≤ n * h := Nat.le_mul_of_pos_right _ hh
  have hb2 : n * (h + 1) ≤ 2 * (N * N * Q) := by
    have : n * (h + 1) = n * h + n := by ring
    have : n * 1 * h = n * h := by ring
    omega
  exact Nat.mul_le_mul_right cGrad.ops hb2


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every iteration, `κ + 1` terms each at most `C N² Q`. -/
theorem SetBasedNet.trainingCost_le_succ (cNeuron cGrad cBack : Cost) {N Q : ℕ} (hN : 1 ≤ N)
    {n k : ℕ} (net : SetBasedNet n k) :
    ∀ h, 1 ≤ h → net.maxWidth ≤ N → h + net.neurons ≤ Q →
      (net.trainingCost cNeuron cGrad cBack h).ops ≤
        (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) *
          (net.depth + 1) := by -- --- PROOF ---
  induction net with
  | @output n =>
      intro h hh hw hq
      -- the loss gradient alone
      have hg := SetBasedNet.aux_output_le cGrad (Q := Q) hN hh (hw : n ≤ N)
        (by have : h + 0 ≤ Q := hq; omega)
      show ((n * (h + 1)) • cGrad).ops ≤ _ * (0 + 1)
      have hsplit : (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) * (0 + 1) =
          2 * (N * N * Q) * cGrad.ops + (cNeuron.ops + 2 * cBack.ops + 40) * (N * N * Q) := by
        ring
      rw [hsplit]
      exact hg.trans (Nat.le_add_right _ _)
  | @linear n m k W b tail ih =>
      intro h hh hw hq
      -- the layer, and the tail at the same generator count
      have hw' : max n tail.maxWidth ≤ N := hw
      have hq' : h + (m + tail.neurons) ≤ Q := hq
      have htail := ih h hh (le_of_max_le_right hw') (by omega)
      have hmN : m ≤ N := by
        cases tail with
        | output => exact le_of_max_le_right hw'
        | linear => exact (le_max_left _ _).trans (le_of_max_le_right hw')
        | nonlinear => exact (le_max_left _ _).trans (le_of_max_le_right hw')
      have hlay := SetBasedNet.aux_linear_le (Q := Q) hN hh hmN (le_of_max_le_left hw')
        (by omega)
      show (Zonotope.mtimesCost m n h + Zonotope.plusCost m + Zonotope.mtimesCost n m h +
          ⟨2 * (m * n * (h + 1)) + 2 * (m * n)⟩ + ⟨2 * m⟩ +
          tail.trainingCost cNeuron cGrad cBack h).ops ≤ _ * (tail.depth + 1 + 1)
      rw [Cost.ops_add]
      -- `C N² Q` more than the tail's bound, of which the layer takes `17 N² Q`
      have hsplit : (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) *
          (tail.depth + 1 + 1) =
          (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) * (tail.depth + 1) +
            (17 * (N * N * Q) + (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 23) * (N * N * Q))
          := by ring
      rw [hsplit]
      omega
  | @nonlinear n k me eLo eUp tail ih =>
      intro h hh hw hq
      -- the layer, and the tail at `n` more generators
      have hw' : max n tail.maxWidth ≤ N := hw
      have hq' : h + (n + tail.neurons) ≤ Q := hq
      have htail := ih (h + n) (by omega) (le_of_max_le_right hw') (by omega)
      have hlay := SetBasedNet.aux_nonlinear_le cNeuron cBack (Q := Q) hN hh
        (le_of_max_le_left hw') (by omega)
      show (Zonotope.imageEnclosureCost n h cNeuron +
          ⟨n * (2 * h + 2) + 10 * (n * (h + 1))⟩ + (n * (h + 1)) • cBack +
          tail.trainingCost cNeuron cGrad cBack (h + n)).ops ≤ _ * (tail.depth + 1 + 1)
      rw [Cost.ops_add]
      have hsplit : (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) *
          (tail.depth + 1 + 1) =
          (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 40) * (N * N * Q) * (tail.depth + 1) +
            ((cNeuron.ops + 10) * (N * N * Q) + 24 * (N * N * Q) + 2 * (N * N * Q) * cBack.ops +
              2 * cGrad.ops * (N * N * Q) + 6 * (N * N * Q)) := by ring
      rw [hsplit]
      omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
