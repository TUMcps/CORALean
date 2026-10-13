module

public import CORALean.ContSet.HPolytope.Float.Operations.CompactZeros
public import CORALean.ContSet.HPolytope.Float.Theorems.DropZerosExact
public import CORALean.ContSet.HPolytope.Float.Theorems.NormalizeRowsOuter

@[expose] public section

/-!
# The float `compactZeros` keeps every point of the polytope in the domain

`dropZeros` is exact (`dropZeros_exact`), so what is left of the outer statement is the
normalization's (`normalizeRows_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactZeros_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆
      (P.compactZeros p dom).construct ∩ dom.construct := by
  intro x hx
  have h := HPolytope.normalizeRows_outer p P dom hx
  unfold HPolytope.compactZeros
  rwa [HPolytope.dropZeros_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
