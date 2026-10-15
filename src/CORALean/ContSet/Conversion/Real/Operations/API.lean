module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_StarSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_StarSet
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SupportFunction
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.StarSet_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_SupportFunction
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Zonotope

/-!
# The constructions of the Real conversions, collected

One file per ordered pair, `<Source>_to_<Target>.lean`, holding what the pair builds, or a section
of `Basic.lean` where the construction is small; what it guarantees is stated and proved in
`Theorems/`, one theorem to a file.
-/
