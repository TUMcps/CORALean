import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset

/-!
# `ConPolyZono.rescaleStep` over a floating-point scalar

One step of the fold `rescale` runs: factor `r` re-parametrized onto `cen r ± rad r` by the
float `getSubset`, the set left alone when `r` is not a factor.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.rescaleStep (cen rad : ℕ → 𝕋) (acc : ConPolyZono 𝕋 (Vec 𝕋 n)) (r : ℕ) :
    ConPolyZono 𝕋 (Vec 𝕋 n) :=
  if h : r < acc.p then acc.getSubset ⟨r, h⟩ (cen r) (rad r) else acc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
