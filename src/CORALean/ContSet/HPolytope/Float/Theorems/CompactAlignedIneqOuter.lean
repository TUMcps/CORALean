module

public import CORALean.ContSet.HPolytope.Float.Operations.CompactAlignedIneq
public import CORALean.ContSet.HPolytope.Float.Theorems.DropAlignedExact
public import CORALean.ContSet.HPolytope.Float.Theorems.NormalizeRowsOuter

@[expose] public section

/-!
# The float `compactAlignedIneq` keeps every point of the polytope in the domain

`dropAligned` is exact (`dropAligned_exact`), so what is left of the outer statement is the
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

theorem HPolytope.compactAlignedIneq_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆
      (P.compactAlignedIneq p dom).construct ∩ dom.construct := by
  intro x hx
  have h := HPolytope.normalizeRows_outer p P dom hx
  unfold HPolytope.compactAlignedIneq
  rwa [HPolytope.dropAligned_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
