import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.NN.Layers.Operations.StarSetFloatRowBounds

/-!
# The float bounds of a neuron hold

Every point of the star set has its neuron `j` between the two bounds.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSetFloat.rowBounds_mem (s : StarSetFloat 𝕋 n) (j : Fin n) {x : Vec ℝ n}
    (hx : x ∈ construct s) :
    toReal (s.rowBounds j).1 ≤ x j ∧ x j ≤ toReal (s.rowBounds j).2 := by -- --- PROOF ---
  obtain ⟨α, hα, -, hxα⟩ := hx
  have hb := fun k => Interval.mul_between_corners (le_refl (toReal (s.G j k)))
    (le_refl (toReal (s.G j k))) (hα k).1 (hα k).2
  rw [hxα j]
  unfold StarSetFloat.rowBounds
  constructor
  · refine le_trans (addDown_le_add _ _) (add_le_add le_rfl ?_)
    exact le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun k _ => (hb k).1)
  · refine le_trans (add_le_add le_rfl ?_) (add_le_addUp _ _)
    exact le_trans (Finset.sum_le_sum fun k _ => (hb k).2) (sum_le_sumUp _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
