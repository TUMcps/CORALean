import CORALean.Float.ContSet.Zonotope.Operations.API

/-!
# What inexact generators cost

Immediate from `abs_sum_le_radius`, the same bound `reduce` uses: what a matrix
reaches on the unit ball is its row sums of absolute values. Here the generators
are known only to within `G` entrywise, there they are exact; the bound does not
care which.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}

theorem Zonotope.mem_generatorError {G : Mat 𝕋 n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hG : ∀ i j, |Δ i j| ≤ toReal (G i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (Zonotope.generatorError G).construct := by
  intro i
  have key := abs_sum_le_radius (fun i j => le_trans (hG i j) (le_abs_self _)) hβ i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ j, Δ i j * β j
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Float
