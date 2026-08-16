import CORALean.Arithmetic.Float.ContSet.Zonotope.API

/-!
# What inexact generators cost

Immediate from `abs_sum_le_radius`, which is the same bound `reduce` uses: what
a matrix can reach on the unit ball is its row sums of absolute values. Here the
generators are known only to within `G` entrywise, there they are exact, and the
bound does not care which.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

theorem mem_generatorError {G : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hG : ∀ i j, |Δ i j| ≤ toReal (G i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (Zonotope.generatorError G).construct := by
  intro i
  have key := abs_sum_le_radius (fun i j => le_trans (hG i j) (le_abs_self _)) hβ i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ j, Δ i j * β j
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Arithmetic.Float.Zonotope.Proofs
