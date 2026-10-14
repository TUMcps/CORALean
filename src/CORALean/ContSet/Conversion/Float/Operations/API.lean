module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_LevelSet
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope

/-!
# The constructions of the Float conversions, collected

One file per ordered pair, `<Source>_to_<Target>.lean`, holding what the pair builds, or a section
of `Basic.lean` where the construction is small; what it guarantees is stated and proved in
`Theorems/`, one theorem to a file.
-/
