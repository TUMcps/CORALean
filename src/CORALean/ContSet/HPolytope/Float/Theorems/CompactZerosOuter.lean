import CORALean.ContSet.HPolytope.Float.Operations.CompactZeros
import CORALean.ContSet.HPolytope.Float.Theorems.DropZerosExact
import CORALean.ContSet.HPolytope.Float.Theorems.NormalizeRowsOuter

/-!
# The float `compactZeros` keeps every point of the polytope in the domain

`dropZeros` is exact (`dropZeros_exact`), so what is left of the outer statement is the
normalization's (`normalizeRows_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactZeros_outer (p : ℕ) (P : HPolytope 𝕋 n) (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆
      (P.compactZeros p dom).construct ∩ dom.construct := by
  intro x hx
  have h := HPolytope.normalizeRows_outer p P dom hx
  unfold HPolytope.compactZeros
  rwa [HPolytope.dropZeros_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
