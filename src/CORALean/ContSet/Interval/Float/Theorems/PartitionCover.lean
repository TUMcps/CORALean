import CORALean.ContSet.Interval.Float.Theorems.PartitionPiece
import CORALean.ContSet.Interval.Real.Theorems.PartitionExact

/-!
# `Interval.partition` covers the box it cuts

The real pieces of the box's reading cover it (`Interval.partition_exact`), and each sits inside
the float piece of the same index (`Interval.partition_piece`), so the float pieces cover the box.
A cover and not a partition, and the pieces overlap by the rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.partition_cover (I : Interval (Vec 𝕋 n)) (splits : ℕ) (hs : 0 < splits) :
    I.nominal.construct ⊆
      ⋃ ind : Fin n → Fin splits, (I.partition splits ind).construct := by -- --- PROOF ---
  -- a point of the box lies in a real piece, hence in the float piece of its index
  intro x hx
  rw [← Real.Interval.partition_exact I.nominal splits hs] at hx
  obtain ⟨ind, hind⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨ind, Interval.partition_piece I splits ind hind⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
