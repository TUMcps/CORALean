module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Union
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The factor vector of the union's second branch

What a point of the second operand is read at in the union: its own factors, the first
operand's at `0`, and both fresh factors at the selector value `t`.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand
* `t` – selector value
* `a₂` – factors of second operand

## Hypotheses
* `ht` – selector value is within the unit interval
* `ha₂` – factors are within the unit interval

## Conclusion
* a factor vector for the second branch exists
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The factor vector of the branch that keeps the second operand: its own factors, the first
operand's pinned to `0`, and the two fresh ones at `t`. -/
theorem ConPolyZono.exists_unionFactors_right {p₁ p₂ : ℕ} (t : ℝ) (ht : |t| ≤ 1)
    {a₂ : Fin p₂ → ℝ} (ha₂ : ∀ k, |a₂ k| ≤ 1) : -- --- CONCL ---
    ∃ a : Fin (p₁ + p₂ + 2) → ℝ, (∀ k, |a k| ≤ 1)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.castAdd p₂ k)) = 0)
      ∧ (∀ k, a (Fin.castAdd 2 (Fin.natAdd p₁ k)) = a₂ k)
      ∧ a (ConPolyZono.unionSel p₁ p₂) = t
      ∧ a (Fin.natAdd (p₁ + p₂) 1) = t := by -- --- PROOF ---
  refine ⟨Fin.append (Fin.append (fun _ => (0:ℝ)) a₂) ![t, t], ?_, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · rw [Fin.append_left]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left]; simp
      · rw [Fin.append_right]; exact ha₂ j
    · rw [Fin.append_right]
      fin_cases k <;> simpa using ht
  · exact fun k => by rw [Fin.append_left, Fin.append_left]
  · exact fun k => by rw [Fin.append_left, Fin.append_right]
  · rw [ConPolyZono.unionSel, Fin.append_right]; rfl
  · rw [Fin.append_right]; rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
