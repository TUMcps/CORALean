import CORALean.ContSet.ZonoBundle.Float.Operations.EnclosingParallelotope
import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude

/-!
# `ZonoBundle.enclosingParallelotope` encloses the bundle

At whichever basis and candidate inverse the check leaves: a point of the bundle has its image
under `H` in the box of the mapped bundle (`mtimes_outer`, `intervalAll_contains`) and its
coordinates within the bundle's box, which is all `parallelotope_contains` asks.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.enclosingParallelotope_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k)
    (Γ : Mat 𝕋 n n) :
    zB.construct ⊆ (zB.enclosingParallelotope hk Γ).construct := by -- --- PROOF ---
  intro x hx
  exact ZonoBundle.parallelotope_contains _ _ _ _
    (ZonoBundle.intervalAll_contains (zB.mtimes _) hk (ZonoBundle.mtimes_outer _ zB ⟨x, hx, rfl⟩))
    (fun j => le_trans (Interval.abs_le_magnitude (ZonoBundle.intervalAll_contains zB hk hx) j)
      (le_maximumOver _ j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
