module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Float.Operations.MatSmul
public import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsMatOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-!
# `Zonotope.matSmul` over-approximates scaling by every scalar in `[cLo, cHi]`

At one scalar `c` in the range, the nominal part scales inside the exact
`Zonotope.map (c • ·)` (`map_exact`), whose center and generators `mul_between_corners`
brackets entry by entry; the box scales by `Interval.smul_outer`.

## Inputs
* `cLo` – lower end of the scalar
* `cHi` – upper end of the scalar
* `c` – scalar
* `Z` – matrix zonotope
* `A` – member matrix

## Hypotheses
* `hcLo` – scalar above the lower end
* `hcHi` – scalar below the upper end
* `hA` – matrix lies in the zonotope

## Conclusion
* scaled member lies in the computed matrix zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matSmul_outer {cLo cHi : 𝕋} {c : ℝ} (hcLo : toReal cLo ≤ c)
    (hcHi : c ≤ toReal cHi) (Z : Zonotope (Mat 𝕋 m n)) {A : Mat ℝ m n}
    (hA : A ∈ Z.construct) : -- --- CONCL ---
    c • A ∈ (Zonotope.matSmul cLo cHi Z).construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hA
  set Zc := CORALean.Real.Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ m n) c) Z.nominal
  have hca : c • a ∈ Zc.construct := by
    rw [← CORALean.Real.Zonotope.map_exact]
    exact ⟨a, ha, rfl⟩
  -- one entry, scaled by the scalar, between the two corner products
  have hentry : ∀ x : 𝕋, toReal (Interval.mulLo cLo cHi x x) ≤ c * toReal x
      ∧ c * toReal x ≤ toReal (Interval.mulHi cLo cHi x x) :=
    fun x => Interval.mul_between_corners hcLo hcHi le_rfl le_rfl
  have hmem := Zonotope.ofEntryBoundsMat_outer Zc (Interval.smul cLo cHi Z.I_error)
    (cLo := fun i j => Interval.mulLo cLo cHi (Z.c i j) (Z.c i j))
    (cHi := fun i j => Interval.mulHi cLo cHi (Z.c i j) (Z.c i j))
    (GLo := fun k i j => Interval.mulLo cLo cHi (Z.G k i j) (Z.G k i j))
    (GHi := fun k i j => Interval.mulHi cLo cHi (Z.G k i j) (Z.G k i j))
    (fun i j => hentry (Z.c i j)) (fun k i j => hentry (Z.G k i j))
    ⟨c • a, hca, c • e, Interval.smul_outer hcLo hcHi Z.I_error he, rfl⟩
  rw [smul_add]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
