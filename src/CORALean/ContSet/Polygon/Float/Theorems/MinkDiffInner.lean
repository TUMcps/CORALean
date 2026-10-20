module

public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner
public import CORALean.ContSet.Polygon.Float.Operations.MinkDiff
public import CORALean.ContSet.Polygon.Float.Theorems.InnerHRepInner

@[expose] public section

/-!
# The float `Polygon.minkDiff` lies in the Minkowski difference

A point of the result lies in one shifted piece; that piece, unshifted, holds the point plus
any point of the subtrahend (`HPolytope.minkDiffOf_inner`, with no equality rows to keep in a
kernel), and lies in its minuend piece (`Polygon.innerHRep_inner`), which lies in the minuend.
Nothing is assumed of the subtrahend: no convexity, no center, no boundary loop.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* the float `Polygon.minkDiff` lies in the Minkowski difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.minkDiff_inner (P Q : Polygon 𝕋) : -- --- CONCL ---
    ContSet.construct (Polygon.minkDiff P Q)
      ⊆ minkowskiDiff (ContSet.construct P) (ContSet.construct Q) := by -- --- PROOF ---
  intro x hx y hy
  obtain ⟨R, hR, hxR⟩ := SetUnion.mem_construct.mp hx
  obtain ⟨p, hp, hpR⟩ := List.mem_filterMap.mp hR
  obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.mp hpR
  -- the description has no equality rows
  have hme : H.me = 0 := by
    simp only [Polygon.innerHRep] at hH
    split_ifs at hH
    cases hH
    rfl
  have hxy := HPolytope.minkDiffOf_inner H _ _ (fun i => absurd i.isLt (by omega)) hxR y hy
  exact SetUnion.mem_construct.mpr ⟨p, hp, Polygon.innerHRep_inner _ hH hxy⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
