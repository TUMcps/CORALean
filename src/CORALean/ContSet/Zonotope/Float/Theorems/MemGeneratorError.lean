module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# What inexact generators cost

Immediate from `abs_sum_le_radius`, the same bound `reduce` uses: what a matrix
reaches on the unit ball is its row sums of absolute values, whether the
generators are exact or known only to within `G` entrywise.

## Inputs
* `G` – stored bound matrix
* `Δ` – generator error matrix
* `β` – factor vector

## Hypotheses
* `hG` – error entries within the stored bounds
* `hβ` – factors in the unit box

## Conclusion
* total error lies in the generator error zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_generatorError {G : Mat 𝕋 n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hG : ∀ i j, |Δ i j| ≤ toReal (G i j)) (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    (fun i => ∑ j, Δ i j * β j) ∈ (Zonotope.generatorError G).construct := by -- --- PROOF ---
  intro i
  have key := abs_sum_le_radius (fun i j => le_trans (hG i j) (le_abs_self _)) hβ i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ j, Δ i j * β j
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
