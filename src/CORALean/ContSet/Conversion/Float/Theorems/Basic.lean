module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeConZonotopeInnerOfSubset
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeConPolyZonoContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeSpectraShadowContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.VPolytope.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `ContSet/Conversion/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =============================  `ConPolyZono.zonotope_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ConPolyZono.zonotope_contains`: its `zonotope` contains it. -/
theorem ConPolyZono.zonotope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.zonotope.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.zonotope_contains

end


section

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===========================  `HPolytope.conZonotopeInner_subset`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Inside `P`, whatever box the conversion is taken at. -/
theorem HPolytope.conZonotopeInner_subset (P : HPolytope 𝕋 (Vec 𝕋 n)) (Bx : Interval (Vec 𝕋 n)) :
    (P.conZonotopeInner Bx).construct ⊆ P.construct :=
  P.conZonotopeInnerOf_subset Bx.zonotope

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- ==============================  `HPolytope.zonotope_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its box, which is what the certificates give. -/
theorem HPolytope.zonotope_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonotope up lo).construct :=
  subset_trans (HPolytope.interval_contains up lo) (Interval.zonotope_contains _)


-- ============================  `HPolytope.polyZonotope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its box's zonotope, whose polynomial-zonotope reading is exact. -/
theorem HPolytope.polyZonotope_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.polyZonotope up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.polyZonotope_contains _)


-- =============================  `HPolytope.conPolyZono_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the polynomial zonotope; the constraint-free embedding is exact. -/
theorem HPolytope.conPolyZono_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conPolyZono up lo).construct :=
  subset_trans (HPolytope.polyZonotope_contains up lo) (PolyZonotope.conPolyZono_contains _)

end


section

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ================================  `Interval.vPolytope_exact`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact for a nonempty box: `vPolytope_contains` and `contains_vPolytope`. -/
theorem Interval.vPolytope_exact (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i)) :
    (Interval.vPolytope I).construct = I.construct :=
  Set.Subset.antisymm (Interval.contains_vPolytope I hI) (Interval.vPolytope_contains I)

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==============================  `VPolytope.interval_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box around the vertices, widened by the error box. Both bounds come from
`SupportBound`, so nothing is computed here. -/
theorem VPolytope.interval_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.interval.construct :=
  Interval.subset_ofBounds _ _

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =============================  `ConZonotope.interval_contains`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Constraints dropped, then the zonotope's own box. -/
theorem ConZonotope.interval_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.interval.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.interval_contains _)


-- =============================  `Interval.conZonotope_contains`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope. The generators absorb the center's rounding there, and the
constraint list stays empty here, so nothing further is paid. -/
theorem Interval.conZonotope_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.conZonotope.construct :=
  subset_trans I.zonotope_contains (Zonotope.conZonotope_contains _)


-- ============================  `Interval.spectraShadow_contains`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope. The generators absorb the center's rounding there, and the
inequality is the exact diagonal one here, so nothing further is paid. -/
theorem Interval.spectraShadow_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.spectraShadow.construct :=
  subset_trans I.zonotope_contains (Zonotope.spectraShadow_contains _)


-- ============================  `PolyZonotope.vPolytope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope enclosure and then that zonotope's rounded sign corners. -/
theorem PolyZonotope.vPolytope_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.vPolytope.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.vPolytope_contains _)


-- =============================  `ConPolyZono.vPolytope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through `ConPolyZono.zonotope`, which drops the constraints, then the zonotope's corners. -/
theorem ConPolyZono.vPolytope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.vPolytope.construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.vPolytope_contains _)


-- ==============================  `VPolytope.zonotope_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its box, the vertices' own error box having already been absorbed
there. -/
theorem VPolytope.zonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_contains (Interval.zonotope_contains _)


-- ==============================  `VPolytope.ellipsoid_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its zonotope, which is its box. -/
theorem VPolytope.ellipsoid_contains (P : VPolytope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : (P.zonotope.h : ℝ) ≤ toReal (mulDown σ σ)) :
    P.construct ⊆ (P.ellipsoid σ).construct :=
  subset_trans P.zonotope_contains (P.zonotope.ellipsoid_contains σ hσ hh)


-- ============================  `VPolytope.polyZonotope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its box's zonotope, whose polynomial-zonotope reading is exact. -/
theorem VPolytope.polyZonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.zonotope_contains (Zonotope.polyZonotope_contains _)


-- =============================  `VPolytope.conPolyZono_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the polynomial zonotope; the constraint-free embedding is exact. -/
theorem VPolytope.conPolyZono_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.conPolyZono.construct :=
  subset_trans P.polyZonotope_contains P.polyZonotope.conPolyZono_contains

end


section

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- ==============================  `Zonotope.hPolytope_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Zonotope.hPolytope_contains`: its `hPolytope` contains it. -/
theorem Zonotope.hPolytope_contains (Z : Zonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    Z.construct ⊆ (Z.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end


section

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =============================  `ConZonotope.hPolytope_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Constraints dropped, then the zonotope answers each direction by summing
absolute values with directed rounding. -/
theorem ConZonotope.hPolytope_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    cZ.construct ⊆ (cZ.hPolytope Aq).construct :=
  subset_trans cZ.zonotope_contains (Zonotope.hPolytope_contains _ _)

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==============================  `Interval.zonoBundle_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the box's own zonotope, then `Zonotope.zonoBundle`, exact by
`Set.iInter_const`. All the loss is the box-to-zonotope step's. -/
theorem Interval.zonoBundle_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.zonoBundle.construct :=
  subset_trans I.zonotope_contains (Zonotope.zonoBundle_exact _).subset


-- =============================  `VPolytope.zonoBundle_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- Through the zonotope the box gives, then `Zonotope.zonoBundle`, exact. All the
loss is the box route's. -/
theorem VPolytope.zonoBundle_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.zonoBundle.construct :=
  subset_trans P.zonotope_contains (Zonotope.zonoBundle_exact _).subset


-- ==============================  `ZonoBundle.zonotope_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Any single member already encloses the whole intersection, so the choice of `i`
owes no proof: the guarantee is sound at every one. -/
theorem ZonoBundle.zonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.zonotope i).construct :=
  Set.iInter_subset _ i


-- =============================  `ZonoBundle.hPolytope_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- Through `ZonoBundle.zonotope i`, then that zonotope's own halfspace description
in the directions the caller names. -/
theorem ZonoBundle.hPolytope_contains {q : ℕ} (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k)
    (Aq : Mat 𝕋 q n) : zB.construct ⊆ (zB.hPolytope i Aq).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.hPolytope_contains _ _)


-- ==============================  `ZonoBundle.interval_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through `ZonoBundle.zonotope i`, then that zonotope's own box. -/
theorem ZonoBundle.interval_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.interval i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.interval_contains _)


-- =============================  `ZonoBundle.vPolytope_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through `ZonoBundle.zonotope i`, then that zonotope's own sign corners. -/
theorem ZonoBundle.vPolytope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.vPolytope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.vPolytope_contains _)

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =============================  `ConPolyZono.interval_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the polynomial zonotope, dropping the constraints, then its box. -/
theorem ConPolyZono.interval_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.interval.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.interval_contains


-- ===========================  `ConZonotope.polyZonotope_contains`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope, dropping the constraints: nothing rounds at either step. -/
theorem ConZonotope.polyZonotope_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.polyZonotope.construct :=
  subset_trans cZ.zonotope_contains cZ.zonotope.polyZonotope_contains


-- =============================  `Interval.conPolyZono_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the polynomial zonotope, the box riding in `err`: nothing rounds. -/
theorem Interval.conPolyZono_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.conPolyZono.construct :=
  subset_trans I.polyZonotope_contains I.polyZonotope.conPolyZono_contains


-- ============================  `ZonoBundle.polyZonotope_contains`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The bundle is the intersection of its members, so any one member, converted, holds
it: nothing rounds. -/
theorem ZonoBundle.polyZonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.polyZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (zB.zonotope i).polyZonotope_contains


-- =============================  `Zonotope.conPolyZono_contains`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the polynomial zonotope: nothing rounds at either step. -/
theorem Zonotope.conPolyZono_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.conPolyZono.construct :=
  subset_trans Z.polyZonotope_contains Z.polyZonotope.conPolyZono_contains


-- ============================  `ZonoBundle.conPolyZono_contains`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Any one member, converted, holds the bundle: nothing rounds. -/
theorem ZonoBundle.conPolyZono_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conPolyZono i).construct :=
  subset_trans (zB.zonotope_contains i) (zB.zonotope i).conPolyZono_contains

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- ============================  `PolyZonotope.hPolytope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope enclosure, then that zonotope's own rounded support bounds; the rows
are the caller's, as in `Zonotope.hPolytope_contains`. -/
theorem PolyZonotope.hPolytope_contains (pZ : PolyZonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    pZ.construct ⊆ (pZ.hPolytope Aq).construct :=
  subset_trans pZ.zonotope_contains (Zonotope.hPolytope_contains _ _)

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n qI : ℕ}


-- =============================  `ConPolyZono.hPolytope_contains`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through `ConPolyZono.zonotope`, which drops the constraints, then the zonotope's halfspaces. -/
theorem ConPolyZono.hPolytope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 qI n) :
    cPZ.construct ⊆ (cPZ.hPolytope Aq).construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.hPolytope_contains _ _)

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
