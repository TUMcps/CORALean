import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend
import CORALean.ContSet.SpectraShadow.Real.Theorems.PosSemidefPlusIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.MtimesExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.CartProdExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
import CORALean.ContSet.SpectraShadow.Real.Theorems.EmptyExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.A0AddSumEq
import CORALean.ContSet.SpectraShadow.Real.Theorems.ProjectExact

/-!
# What a spectrahedral shadow guarantees, collected

`plus`, `map`, `mtimes` and `cartProd` exactly, each as an equation of sets, and
convexity unconditionally. `lmi_append` and `posSemidef_plus_iff` say that `plus`'s
inequality is the two it came from, which the float layer reuses. Nothing here is an
enclosure: a spectrahedral shadow is closed under every operation computed here.
-/
