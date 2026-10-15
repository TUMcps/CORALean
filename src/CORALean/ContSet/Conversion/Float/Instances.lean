module

public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.Capsule.Float.Instances
public import CORALean.ContSet.ConPolyZono.Float.Instances
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.VPolytope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Definitions.IntervalOuter
public import CORALean.ContSet.Conversion.Float.Definitions.OfInterval

@[expose] public section

/-!
# The box classes over a floating-point scalar, at each representation

The instances of `IntervalOuter` and `OfInterval` over `𝕋`, here and not with the classes in
`Definitions/` because each field is the guarantee of a conversion.

The instance list is the exact layer's, minus `HPolytope`: a box from halfspaces
is `2n` linear programs, so `interval` there takes certificates and is no function
of the representation alone. A vertex list needs none (`boundProj`/`boundNegProj`).

An exact representation is one at `𝕋 := ℝ`, through its own class: that is what lets an
algorithm written once over the scalar run on `Real.Zonotope` as well as on a float one.

Nothing here rounds. The box arrives already in `𝕋`, and each conversion pays
whatever its own centering costs — `Interval.zonotope` measures its radius from
the center it actually stored, so the box is covered by the generators alone.

An exact representation is one at `𝕋 := ℝ`, through its own class, as in
the exact layer.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- A box is its own. -/
instance : IntervalOuter ℐ𝒱[𝕋] 𝕋 where
  interval I := I
  interval_outer _ := subset_rfl

instance : IntervalOuter 𝒵[𝕋] 𝕋 where
  interval Z := Z.interval
  interval_outer Z := Zonotope.interval_contains Z

instance : IntervalOuter (fun n => ConZonotope 𝕋 (Vec 𝕋 n)) 𝕋 where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_contains C

instance : IntervalOuter (fun n => Capsule 𝕋 n) 𝕋 where
  interval C := C.interval
  interval_outer C := Capsule.interval_contains C

instance : IntervalOuter (fun n => ConPolyZono 𝕋 (Vec 𝕋 n)) 𝕋 where
  interval C := C.interval
  interval_outer C := ConPolyZono.interval_contains C

instance : IntervalOuter 𝒫𝒵[𝕋] 𝕋 where
  interval P := P.interval
  interval_outer P := PolyZonotope.interval_contains P

/-- The box of a vertex list: the bounds `boundProj`/`boundNegProj` of every coordinate. -/
instance : IntervalOuter 𝒱𝒫[𝕋] 𝕋 where
  interval P := P.interval
  interval_outer P := VPolytope.interval_contains P

/-- An exact representation boxes itself at `𝕋 := ℝ`, the box its exact class returns. -/
instance {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S] :
    IntervalOuter S ℝ where
  interval s := ⟨(Real.IntervalOuter.interval s).inf, (Real.IntervalOuter.interval s).sup⟩
  interval_outer s := Real.IntervalOuter.interval_outer s

instance : OfInterval ℐ𝒱[𝕋] 𝕋 where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

instance : OfInterval 𝒵[𝕋] 𝕋 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.zonotope_contains I

instance : OfInterval (fun n => ConZonotope 𝕋 (Vec 𝕋 n)) 𝕋 where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.conZonotope_contains I

instance : OfInterval 𝒫𝒵[𝕋] 𝕋 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.polyZonotope_contains I

/-- An exact representation absorbs a box at `𝕋 := ℝ` through its exact class, the box's
bounds being real already. -/
instance {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] :
    OfInterval S ℝ where
  ofInterval I := Real.OfInterval.ofInterval ⟨I.inf, I.sup⟩
  ofInterval_outer I := Real.OfInterval.ofInterval_outer ⟨I.inf, I.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
