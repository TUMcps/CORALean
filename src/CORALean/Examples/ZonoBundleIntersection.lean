import CORALean.ContSet.ZonoBundle.Real.Instances
import CORALean.ContSet.SetIntersection.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Two zonotopes whose intersection is not one, bundled exactly

A box and a diamond centered off it: their intersection has no center of
symmetry, so no `Zonotope` denotes it, where `ZonoBundle.intersection_exact` denotes it
outright — `intersection`, not merely `intersection_outer`. `Plus` and `Mtimes` still run at a
bundle exactly as at any other `ContSet`, which is the second point: a bundle
pays for its exact intersection with nothing else.

`CompactSet` is a theorem here, the general `SetIntersection.isCompact_construct`, and not an
instance: `ZonoBundle.construct` at `k = 0` is `⋂` over the empty family, which is `univ`,
not compact, so the class's unconditional obligation has no proof to give it. A
member is what the theorem asks for instead.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet

-- A unit box at the origin, and a unit diamond centered away from it, sharing no center.

def Example.box : Zonotope (Vec ℝ 2) := ⟨2, ![0, 0], ![![1, 0], ![0, 1]]⟩

noncomputable def Example.diamond : Zonotope (Vec ℝ 2) := ⟨2, ![(1:ℝ)/2, 1/2], ![![1, 1], ![1, -1]]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def Example.boxBundle : ZonoBundle (Vec ℝ 2) := ⟨1, fun _ => Example.box⟩
noncomputable def Example.diamondBundle : ZonoBundle (Vec ℝ 2) := ⟨1, fun _ => Example.diamond⟩

-- anonymous, since their content is that they elaborate at this bundle

/-- Exact, where a single zonotope holding the box and the diamond could only
have enclosed. -/
example :
    (Example.boxBundle.intersection Example.diamondBundle).construct
      = Example.boxBundle.construct ∩ Example.diamondBundle.construct :=
  ZonoBundle.intersection_exact Example.boxBundle Example.diamondBundle

/-- The same fact, read through the generic `Intersection` class rather than the bundle's
own theorem: no use site needs to know it is exact to call it. -/
example :
    construct Example.boxBundle ∩ construct Example.diamondBundle
      ⊆ construct (Intersection.intersection Example.boxBundle Example.diamondBundle) :=
  Intersection.intersection_outer Example.boxBundle Example.diamondBundle

/-- `plus`, at a bundle like at any other representation. -/
example :
    construct Example.boxBundle + construct Example.diamondBundle
      ⊆ construct (Plus.plus Example.boxBundle Example.diamondBundle) :=
  Plus.plus_outer Example.boxBundle Example.diamondBundle

/-- `mtimes` too, for any matrix — `S` named, as every generic family use
site has to. -/
example (M : Mat ℝ 2 2) :
    (⋃ A ∈ construct M, (A *ᵥ ·) '' construct Example.boxBundle)
      ⊆ construct (Mtimes.mtimes (S := 𝒵ℬ) M Example.boxBundle) :=
  Mtimes.mtimes_outer (S := 𝒵ℬ) M Example.boxBundle

/-- Compact, since this bundle's `k` is `1`, not `0`. -/
example : IsCompact Example.boxBundle.construct :=
  SetIntersection.isCompact_construct (I := Example.boxBundle.toSetIntersection)
    (by simp [Example.boxBundle, ZonoBundle.toSetIntersection])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
