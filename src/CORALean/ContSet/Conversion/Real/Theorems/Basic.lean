module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalLevelSetExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmPolyZonotopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePolyZonotopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Theorems.SubsetOfBounds
public import CORALean.ContSet.LevelSet.Real.Theorems.AndExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic
public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.BlockDiag
public import CORALean.Global.Corners
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `ContSet/Conversion/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {n : ℕ}


-- =============================  `Ellipsoid.conZonotope_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through the zonotope; the constrained zonotope with nothing to satisfy loses nothing. -/
theorem Ellipsoid.conZonotope_contains (E : Ellipsoid n) : E.construct ⊆ E.conZonotope.construct :=
  subset_trans E.zonotope_contains (Zonotope.conZonotope_exact _).subset


-- ==============================  `Ellipsoid.interval_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- `Ellipsoid.interval_contains`: its `interval` contains it. -/
theorem Ellipsoid.interval_contains (E : Ellipsoid n) : E.construct ⊆ E.interval.construct :=
  Interval.subset_ofBounds _ _


-- =============================  `Interval.polyZonotope_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---

/-- `Interval.polyZonotope_contains`: its `polyZonotope` contains it. -/
theorem Interval.polyZonotope_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.polyZonotope.construct :=
  subset_trans I.zonotope_contains (Zonotope.polyZonotope_exact _).subset


-- ================================  `Interval.polyZonotope_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---

/-- A box as a polynomial zonotope: `polyZonotope_h` -/
theorem Interval.polyZonotope_h (I : Interval (Vec ℝ n)) : I.polyZonotope.h = n := rfl


-- ================================  `Interval.polyZonotope_p`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---

/-- One factor and one dependent generator per coordinate — `Interval.zonotope`'s
own count, `Zonotope.polyZonotope` carrying it across unchanged. -/
theorem Interval.polyZonotope_p (I : Interval (Vec ℝ n)) : I.polyZonotope.p = n := rfl


-- ================================  `Interval.polyZonotope_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---

/-- No independent generators, `Zonotope.polyZonotope` making every one dependent. -/
theorem Interval.polyZonotope_q (I : Interval (Vec ℝ n)) : I.polyZonotope.q = 0 := rfl


-- ==============================  `PolyLevelSet.levelSet_exact`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- The polynomial level set and its level set denote one set, the box's rows meeting its box, so
everything proved of a `LevelSet` holds of it. -/
theorem PolyLevelSet.levelSet_exact (P : PolyLevelSet n) : P.levelSet.construct = P.construct := by
  rw [PolyLevelSet.levelSet, LevelSet.and_exact, Interval.levelSet_exact]
  rfl


-- =============================  `PolyZonotope.interval_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---

/-- `PolyZonotope.interval_contains`: its `interval` contains it. -/
theorem PolyZonotope.interval_contains (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.interval.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.interval_contains _)


-- ==============================  `VPolytope.zonotope_contains`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Through its box. A tighter zonotope enclosure of a vertex list is a fitting
problem rather than a conversion, so the box is what a definition can give. -/
theorem VPolytope.zonotope_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_contains (Interval.zonotope_contains _)


-- =============================  `ZonoBundle.vPolytopeAll_exact`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact: the vertex list spans the bundle. -/
theorem ZonoBundle.vPolytopeAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : (zB.vPolytopeAll hk hne).construct = zB.construct :=
  (ConZonotope.vPolytope_exact _ _).trans (ZonoBundle.conZonotopeAll_exact zB hk)

end


section

open Matrix

variable {n : ℕ}


-- ================================  `HPolytope.eq_sum_single`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A coefficient vector is the combination of the unit vectors it names. -/
theorem HPolytope.eq_sum_single (β : Fin n → ℝ) :
    β = ∑ i, β i • (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]


-- ========================  `SpectraShadow.supportFunc_eq_coe_toReal`  ========================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A finite support value of a nonempty set is the real it reads as. -/
theorem SpectraShadow.supportFunc_eq_coe_toReal {α : Type} [AddCommGroup α] [Module ℝ α]
    (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) (hne : S.construct ≠ ∅)
    (hfin : S.supportFunc c ≠ ⊤) : S.supportFunc c = ((S.supportFunc c).toReal : ℝ) :=
  (EReal.coe_toReal hfin (fun h => hne ((S.supportFunc_eq_bot_iff c).mp h))).symm

end


section

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- ============================  `HPolytope.isCompact_of_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Bounded because something bounded contains it, which is what an enclosure
already computed says. -/
theorem HPolytope.isCompact_of_contains {W : VPolytope (Vec ℝ n)} (h : P.construct ⊆ W.construct) :
    IsCompact P.construct :=
  Metric.isCompact_of_isClosed_isBounded P.isClosed_construct (W.isBounded_construct.subset h)


-- ===============================  `HPolytope.vPolytope_exact`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `HPolytope.vPolytope_exact`: its `vPolytope` is exactly it. -/
theorem HPolytope.vPolytope_exact (P : HPolytope (Vec ℝ n)) (hc : IsCompact P.construct)
    (hne : P.construct.Nonempty) : (P.vPolytope hne).construct = P.construct :=
  Set.Subset.antisymm (P.contains_vPolytope hne) (P.vPolytope_contains hc hne)

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ============================  `PolyZonotope.vPolytope_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---

/-- `PolyZonotope.vPolytope_contains`: its `vPolytope` contains it. -/
theorem PolyZonotope.vPolytope_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.vPolytope.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.vPolytope_contains _)

end


section

variable {n m : ℕ}


-- ================================  `Taylm.conPolyZono_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `conPolyZono(taylm)`, which goes through `polyZonotope` and adds no constraint;
exact where that is. -/
theorem Taylm.conPolyZono_exact (T : Fin m → Taylm n) (hT : ∀ i, (T i).rem.inf ≤ (T i).rem.sup) :
    (Taylm.conPolyZono T).construct = Taylm.construct T :=
  ((Taylm.polyZonotope T).conPolyZono_exact).symm.trans (Taylm.polyZonotope_exact T hT)

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- ============================  `VPolytope.polyZonotope_contains`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---

/-- `VPolytope.polyZonotope_contains`: its `polyZonotope` contains it. -/
theorem VPolytope.polyZonotope_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.zonotope_contains (Zonotope.polyZonotope_exact _).subset

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
