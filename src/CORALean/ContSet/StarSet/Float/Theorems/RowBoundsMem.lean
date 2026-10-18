module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.StarSet.Float.Operations.RowBounds

@[expose] public section

/-!
# The float bounds of a neuron hold

Every point of the nominal star set has its neuron `j` between the two bounds. The bounds are
those of the stored numbers and leave `I_error` out, which a caller adds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.rowBounds_mem (s : StarSet 𝕋 n) (j : Fin n) {x : Vec ℝ n}
    (hx : x ∈ s.nominal.construct) :
    toReal (s.rowBounds j).inf ≤ x j ∧ x j ≤ toReal (s.rowBounds j).sup := by -- --- PROOF ---
  obtain ⟨α, ⟨hα, -⟩, hxα⟩ := hx
  have hb := fun k => Interval.mul_between_corners (le_refl (toReal (s.G j k)))
    (le_refl (toReal (s.G j k))) (hα k).1 (hα k).2
  rw [hxα j]
  unfold StarSet.rowBounds
  constructor
  · refine le_trans (addDown_le_add _ _) (add_le_add le_rfl ?_)
    exact le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun k _ => (hb k).1)
  · refine le_trans (add_le_add le_rfl ?_) (add_le_addUp _ _)
    exact le_trans (Finset.sum_le_sum fun k _ => (hb k).2) (sum_le_sumUp _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
