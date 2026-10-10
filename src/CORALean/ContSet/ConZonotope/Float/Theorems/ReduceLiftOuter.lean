import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLift
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftByOuter

/-!
# `ConZonotope.reduceLift` over-approximates, in floats

Above the generator count it is `reduceLiftBy_outer` at the partition Girard's rule chose
for the lifted zonotope; at or below it, the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLift_outer (cZ : ConZonotope 𝕋 n) (o : ℕ) :
    cZ.construct ⊆ (cZ.reduceLift o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduceLift
  simp only []
  split_ifs with hlt
  · exact ConZonotope.reduceLiftBy_outer cZ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
