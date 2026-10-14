module

public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalConZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Definitions.IntervalOuter
public import CORALean.ContSet.Conversion.Real.Definitions.OfInterval

@[expose] public section

/-!
# The box classes, at each representation

The instances of `IntervalOuter` and `OfInterval`, here and not with the classes in `Definitions/`
because each field is the guarantee of a conversion.

Not every representation has one, and that is the point: `HPolytope` reaches
its box through `2n` linear programs, so its `interval` takes the certificates
as arguments and cannot be a total function of the representation alone. A pipeline
that wants them supplies the box itself.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  INSTANCES  ========================================= --

/-- A box is its own. -/
instance : IntervalOuter (ℐ𝒱) where
  interval I := I
  interval_outer _ := subset_rfl

instance : IntervalOuter 𝒵 where
  interval Z := Z.interval
  interval_outer Z := Zonotope.interval_contains Z

instance : IntervalOuter (𝒞) where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_contains C

instance : IntervalOuter (fun n => Capsule n) where
  interval C := C.interval
  interval_outer C := Capsule.interval_contains C

instance : IntervalOuter (𝒞𝒫𝒵) where
  interval C := C.interval
  interval_outer C := ConPolyZono.interval_contains C

instance : IntervalOuter (𝒫𝒵) where
  interval P := P.interval
  interval_outer P := PolyZonotope.interval_contains P

/-- The box of a vertex list: the extreme coordinates of its vertices. -/
noncomputable instance : IntervalOuter (𝒱𝒫) where
  interval P := P.interval
  interval_outer P := VPolytope.interval_contains P

instance : OfInterval (ℐ𝒱) where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

noncomputable instance : OfInterval 𝒵 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.zonotope_contains I

noncomputable instance : OfInterval (𝒞) where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.conZonotope_contains I

noncomputable instance : OfInterval 𝒫𝒵 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.polyZonotope_contains I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
