module

public import CORALean.ContSet.ZonoBundle.Float.Operations.EnclosingParallelotope
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude

@[expose] public section

/-!
# `ZonoBundle.enclosingParallelotope` encloses the bundle

At whichever basis and candidate inverse the check leaves: a point of the bundle has its image
under `H` in the box of the mapped bundle (`SetIntersection.memberwise_outer` at
`Zonotope.mtimes_outer`, then `intervalAll_contains`) and its coordinates within the bundle's
box, which is all `parallelotope_contains` asks.

## Inputs
* `zB` – float zonotope bundle
* `Γ` – edge directions

## Hypotheses
* `hk` – the bundle has a member

## Conclusion
* the bundle is contained in the parallelotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.enclosingParallelotope_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k)
    (Γ : Mat 𝕋 n n) : -- --- CONCL ---
    zB.construct ⊆ (zB.enclosingParallelotope hk Γ).construct := by -- --- PROOF ---
  intro x hx
  exact ZonoBundle.parallelotope_contains _ _ _ _
    (ZonoBundle.intervalAll_contains (zB.mtimes _) hk
      (SetIntersection.memberwise_outer (Set.image (toRealMat _ *ᵥ ·)) Set.monotone_image
        (fun i => ⟨i, Zonotope.mtimes_outer _ (zB.Z i)⟩) ⟨x, hx, rfl⟩))
    (fun j => le_trans (Interval.abs_le_magnitude (ZonoBundle.intervalAll_contains zB hk hx) j)
      (le_maximumOver _ j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
