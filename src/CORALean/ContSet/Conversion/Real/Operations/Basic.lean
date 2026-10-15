module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `ContSet/Conversion/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {n : ℕ}


-- ====================================  `Capsule.interval`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a box -/
def Capsule.interval (C : Capsule n) : Interval (Vec ℝ n) :=
  ⟨fun i => C.c i - (|C.g i| + C.r), fun i => C.c i + (|C.g i| + C.r)⟩


-- ===================================  `Capsule.hPolytope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a halfspace description -/
noncomputable def Capsule.hPolytope (C : Capsule n) : HPolytope (Vec ℝ n) :=
  C.interval.hPolytope


-- ===================================  `Capsule.vPolytope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a vertex description -/
noncomputable def Capsule.vPolytope (C : Capsule n) : VPolytope (Vec ℝ n) :=
  C.interval.vPolytope


-- ====================================  `Capsule.zonotope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a zonotope -/
noncomputable def Capsule.zonotope (C : Capsule n) : Zonotope (Vec ℝ n) :=
  C.interval.zonotope


-- ==================================  `ConPolyZono.interval`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as a box -/
def ConPolyZono.interval (cPZ : ConPolyZono (Vec ℝ n)) : Interval (Vec ℝ n) :=
  cPZ.polyZonotope.interval

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =================================  `ConPolyZono.vPolytope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as its corners -/
noncomputable def ConPolyZono.vPolytope (cPZ : ConPolyZono α) : VPolytope α :=
  cPZ.polyZonotope.vPolytope


-- ==================================  `ConPolyZono.zonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as a zonotope -/
def ConPolyZono.zonotope (cPZ : ConPolyZono α) : Zonotope α :=
  cPZ.polyZonotope.zonotope


-- ==================================  `ConZonotope.zonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- Dropping the constraints -/
def ConZonotope.zonotope (cZ : ConZonotope α) : Zonotope α where
  h := cZ.h
  c := cZ.c
  G := cZ.G

end


section

variable {n : ℕ}


-- =================================  `ConZonotope.ellipsoid`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as an ellipsoid -/
noncomputable def ConZonotope.ellipsoid (cZ : ConZonotope (Vec ℝ n)) : Ellipsoid n :=
  cZ.zonotope.ellipsoid


-- ==================================  `ConZonotope.interval`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a box -/
def ConZonotope.interval (cZ : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  cZ.zonotope.interval

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `ConZonotope.polyZonotope`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a polynomial zonotope -/
def ConZonotope.polyZonotope (cZ : ConZonotope α) : PolyZonotope α :=
  cZ.zonotope.polyZonotope

end


section

variable {n : ℕ}


-- =================================  `Ellipsoid.conZonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as a constrained zonotope -/
noncomputable def Ellipsoid.conZonotope (E : Ellipsoid n) : ConZonotope (Vec ℝ n) :=
  E.zonotope.conZonotope

end


section

open Matrix CORALean

variable {n : ℕ}


-- ===================================  `Ellipsoid.levelSet`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `levelSet(E)`: the single constraint `(x - q)ᵀ (G Gᵀ)⁻¹ (x - q) - 1 ≤ 0`. -/
noncomputable def Ellipsoid.levelSet (E : Ellipsoid n) : LevelSet n where
  m := 1
  f x := fun _ => (x - E.c) ⬝ᵥ ((E.G * E.Gᵀ)⁻¹ *ᵥ (x - E.c)) - 1
  op := fun _ => .le

end


section

variable {n : ℕ}


-- =================================  `Ellipsoid.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as a polynomial zonotope -/
noncomputable def Ellipsoid.polyZonotope (E : Ellipsoid n) : PolyZonotope (Vec ℝ n) :=
  E.zonotope.polyZonotope


-- ==================================  `Ellipsoid.vPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as its corners -/
noncomputable def Ellipsoid.vPolytope (E : Ellipsoid n) : VPolytope (Vec ℝ n) :=
  E.zonotope.vPolytope

end


section

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- ===================================  `HPolytope.interval`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a box -/
def HPolytope.interval (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Interval (Vec ℝ n) :=
  Interval.ofBounds up lo

end


section

variable {n : ℕ}


-- ===================================  `HPolytope.levelSet`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `levelSet(P)`: `A x - b ≤ 0` stacked on `Ae x - be = 0`. -/
def HPolytope.levelSet (P : HPolytope (Vec ℝ n)) : LevelSet n where
  m := P.m + P.me
  f x := Fin.append (fun i => P.A i x - P.b i) (fun j => P.Ae j x - P.be j)
  op := Fin.append (fun _ => .le) (fun _ => .eq)

end


section

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- ===================================  `HPolytope.zonotope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a zonotope -/
noncomputable def HPolytope.zonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Zonotope (Vec ℝ n) :=
  (HPolytope.interval up lo).zonotope


-- ==================================  `HPolytope.ellipsoid`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as an ellipsoid -/
noncomputable def HPolytope.ellipsoid (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Ellipsoid n :=
  (HPolytope.zonotope up lo).ellipsoid


-- =================================  `HPolytope.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a polynomial zonotope -/
noncomputable def HPolytope.polyZonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : PolyZonotope (Vec ℝ n) :=
  (HPolytope.zonotope up lo).polyZonotope


-- =================================  `HPolytope.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a constrained polynomial zonotope -/
noncomputable def HPolytope.conPolyZono (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ConPolyZono (Vec ℝ n) :=
  (HPolytope.polyZonotope up lo).conPolyZono

end


section

variable {n : ℕ}


-- ==================================  `Interval.conZonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a constrained zonotope -/
noncomputable def Interval.conZonotope (I : Interval (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  I.zonotope.conZonotope


-- ===================================  `Interval.ellipsoid`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as an ellipsoid -/
noncomputable def Interval.ellipsoid (I : Interval (Vec ℝ n)) : Ellipsoid n :=
  I.zonotope.ellipsoid


-- ===================================  `Capsule.ellipsoid`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as an ellipsoid -/
noncomputable def Capsule.ellipsoid (C : Capsule n) : Ellipsoid n :=
  C.interval.ellipsoid

end


section

open Entrywise

variable {n : ℕ}


-- ===================================  `Interval.levelSet`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box as `inf - x ≤ 0` stacked on `x - sup ≤ 0`. -/
def Interval.levelSet (I : Interval (Vec ℝ n)) : LevelSet n where
  m := n + n
  f x := Fin.append (fun i => I.inf i - x i) (fun i => x i - I.sup i)
  op := Fin.append (fun _ => .le) (fun _ => .le)

end


section

variable {n : ℕ}


-- =================================  `Interval.polyZonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---

/-- A box as a polynomial zonotope -/
noncomputable def Interval.polyZonotope (I : Interval (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  I.zonotope.polyZonotope


-- ==================================  `Capsule.polyZonotope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a polynomial zonotope -/
noncomputable def Capsule.polyZonotope (C : Capsule n) : PolyZonotope (Vec ℝ n) :=
  C.interval.polyZonotope


-- ==================================  `Interval.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a constrained polynomial zonotope -/
noncomputable def Interval.conPolyZono (I : Interval (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  I.polyZonotope.conPolyZono


-- ==================================  `Capsule.conPolyZono`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a constrained polynomial zonotope -/
noncomputable def Capsule.conPolyZono (C : Capsule n) : ConPolyZono (Vec ℝ n) :=
  C.interval.conPolyZono


-- =================================  `Interval.spectraShadow`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a spectrahedral shadow -/
noncomputable def Interval.spectraShadow (I : Interval (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  I.zonotope.spectraShadow


-- =================================  `Capsule.spectraShadow`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a spectrahedral shadow -/
noncomputable def Capsule.spectraShadow (C : Capsule n) : SpectraShadow (Vec ℝ n) :=
  C.interval.spectraShadow


-- =====================================  `Interval.taylm`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as an array of Taylor models -/
noncomputable def Interval.taylm (I : Interval (Vec ℝ n)) (N : ℕ) : Fin n → Taylm n :=
  fun i => ⟨[((I.inf i + I.sup i) / 2, 0), ((I.sup i - I.inf i) / 2, Pi.single i 1)], ⟨0, 0⟩, N⟩

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `PolyZonotope.conZonotope`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as a constrained zonotope -/
def PolyZonotope.conZonotope (pZ : PolyZonotope α) : ConZonotope α :=
  pZ.zonotope.conZonotope


-- ================================  `ConPolyZono.conZonotope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as a constrained zonotope -/
def ConPolyZono.conZonotope (cPZ : ConPolyZono α) : ConZonotope α :=
  cPZ.polyZonotope.conZonotope

end


section

variable {n : ℕ}


-- =================================  `PolyZonotope.ellipsoid`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as an ellipsoid -/
noncomputable def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec ℝ n)) : Ellipsoid n :=
  pZ.zonotope.ellipsoid


-- =================================  `ConPolyZono.ellipsoid`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as an ellipsoid -/
noncomputable def ConPolyZono.ellipsoid (cPZ : ConPolyZono (Vec ℝ n)) : Ellipsoid n :=
  cPZ.polyZonotope.ellipsoid

end


section

variable {m : ℕ}


-- ===================================  `PolyZonotope.taylm`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as an array of Taylor models -/
def PolyZonotope.taylm (pZ : PolyZonotope (Vec ℝ m)) (N : ℕ) : Fin m → Taylm (pZ.p + pZ.q) :=
  fun i => ⟨(pZ.c i, 0) :: (List.ofFn (fun j => (pZ.G j i, Fin.append (fun k => pZ.E k j) 0))
    ++ List.ofFn (fun l => (pZ.GI l i, Pi.single (Fin.natAdd pZ.p l) 1))), ⟨0, 0⟩, N⟩

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===============================  `SpectraShadow.conZonotope`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a conZonotope -/
noncomputable def SpectraShadow.conZonotope (S : SpectraShadow α) : ConZonotope α :=
  S.zonotope.conZonotope


-- ===============================  `SpectraShadow.polyZonotope`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a polyZonotope -/
noncomputable def SpectraShadow.polyZonotope (S : SpectraShadow α) : PolyZonotope α :=
  S.zonotope.polyZonotope

end


section

variable {n m : ℕ}


-- ===================================  `Taylm.conPolyZono`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An array of Taylor models as a constrained polynomial zonotope -/
noncomputable def Taylm.conPolyZono (T : Fin m → Taylm n) : ConPolyZono (Vec ℝ m) :=
  (Taylm.polyZonotope T).conPolyZono

end


section

variable {n : ℕ}


-- =====================================  `Taylm.interval`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An array of Taylor models as a box -/
def Taylm.interval {m : ℕ} (T : Fin m → Taylm n) : Interval (Vec ℝ m) :=
  ⟨fun i => (T i).bounds.1, fun i => (T i).bounds.2⟩

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- ==================================  `VPolytope.hPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Vertices to halfspaces -/
noncomputable def VPolytope.hPolytope (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  HPolytope.ofBounds Aq fun i => P.supportBound (Aq i)

end


section

variable {n : ℕ}


-- ===================================  `VPolytope.interval`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a box -/
noncomputable def VPolytope.interval (P : VPolytope (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => ⨅ l, P.V l i
  sup := fun i => ⨆ l, P.V l i


-- ===================================  `VPolytope.zonotope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a zonotope -/
noncomputable def VPolytope.zonotope (P : VPolytope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  P.interval.zonotope


-- ==================================  `VPolytope.ellipsoid`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as an ellipsoid -/
noncomputable def VPolytope.ellipsoid (P : VPolytope (Vec ℝ n)) : Ellipsoid n :=
  P.zonotope.ellipsoid

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- =================================  `VPolytope.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---

/-- A hull as a polynomial zonotope -/
noncomputable def VPolytope.polyZonotope (P : VPolytope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  P.zonotope.polyZonotope

end


section

variable {n : ℕ}


-- =================================  `VPolytope.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a constrained polynomial zonotope -/
noncomputable def VPolytope.conPolyZono (P : VPolytope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  P.polyZonotope.conPolyZono


-- ================================  `ZonoBundle.spectraShadow`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope bundle as a spectrahedral shadow -/
def ZonoBundle.spectraShadow (zB : ZonoBundle (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  match List.ofFn fun i => (zB.Z i).spectraShadow with
  | [] => SpectraShadow.Inf n                    -- no member: the whole space
  | S :: Ss => Ss.foldl SpectraShadow.inter S    -- `and_` of the members, in order

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ==================================  `ZonoBundle.zonotope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One component of a bundle, enclosing it -/
def ZonoBundle.zonotope (zB : ZonoBundle α) (i : Fin zB.k) : Zonotope α := zB.Z i

end


section

variable {n : ℕ}


-- ==================================  `ZonoBundle.ellipsoid`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's ellipsoid, at one component -/
noncomputable def ZonoBundle.ellipsoid (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) : Ellipsoid n :=
  (zB.zonotope i).ellipsoid


-- ==================================  `ZonoBundle.interval`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's box, at one component -/
def ZonoBundle.interval (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) : Interval (Vec ℝ n) :=
  (zB.zonotope i).interval

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `ZonoBundle.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's polynomial zonotope, at one component -/
def ZonoBundle.polyZonotope (zB : ZonoBundle α) (i : Fin zB.k) : PolyZonotope α :=
  (zB.zonotope i).polyZonotope

end


section

variable {n : ℕ}


-- ====================================  `Zonotope.capsule`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a capsule -/
noncomputable def Zonotope.capsule (Z : Zonotope (Vec ℝ n)) : Capsule n :=
  Z.interval.capsule

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ==================================  `Zonotope.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a constrained polynomial zonotope -/
def Zonotope.conPolyZono (Z : Zonotope α) : ConPolyZono α :=
  Z.polyZonotope.conPolyZono


-- ===============================  `SpectraShadow.conPolyZono`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a conPolyZono -/
noncomputable def SpectraShadow.conPolyZono (S : SpectraShadow α) : ConPolyZono α :=
  S.zonotope.conPolyZono


-- =================================  `ZonoBundle.conPolyZono`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's constrained polynomial zonotope, at one component -/
def ZonoBundle.conPolyZono (zB : ZonoBundle α) (i : Fin zB.k) : ConPolyZono α :=
  (zB.zonotope i).conPolyZono

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- ===================================  `Zonotope.hPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as halfspaces -/
def Zonotope.hPolytope (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => Z.supportBound (Aq i)


-- =================================  `ConZonotope.hPolytope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as halfspaces -/
def ConZonotope.hPolytope (cZ : ConZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  cZ.zonotope.hPolytope Aq

end


section

variable {n q : ℕ}


-- ==================================  `Ellipsoid.hPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as halfspaces -/
noncomputable def Ellipsoid.hPolytope (E : Ellipsoid n) (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    HPolytope (Vec ℝ n) :=
  E.zonotope.hPolytope Aq

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =================================  `PolyZonotope.hPolytope`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as halfspaces -/
def PolyZonotope.hPolytope (pZ : PolyZonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  pZ.zonotope.hPolytope Aq

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α] {qI : ℕ}


-- =================================  `ConPolyZono.hPolytope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as halfspaces -/
noncomputable def ConPolyZono.hPolytope (cPZ : ConPolyZono α) (Aq : Fin qI → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  cPZ.polyZonotope.hPolytope Aq

end


section

variable {n q : ℕ}


-- ==================================  `ZonoBundle.hPolytope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's halfspaces, at one component -/
def ZonoBundle.hPolytope (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k)
    (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) : HPolytope (Vec ℝ n) :=
  (zB.zonotope i).hPolytope Aq

end


section

variable {n : ℕ}


-- =====================================  `Zonotope.taylm`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as an array of Taylor models -/
def Zonotope.taylm {m : ℕ} (Z : Zonotope (Vec ℝ m)) (N : ℕ) : Fin m → Taylm Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)), ⟨0, 0⟩, N⟩

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ==================================  `Zonotope.zonoBundle`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope is a bundle of one -/
def Zonotope.zonoBundle (Z : Zonotope α) : ZonoBundle α := ⟨1, fun _ => Z⟩


-- =================================  `ConPolyZono.zonoBundle`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as a bundle of one -/
def ConPolyZono.zonoBundle (cPZ : ConPolyZono α) : ZonoBundle α :=
  cPZ.zonotope.zonoBundle


-- =================================  `ConZonotope.zonoBundle`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a bundle of one -/
def ConZonotope.zonoBundle (cZ : ConZonotope α) : ZonoBundle α :=
  cZ.zonotope.zonoBundle

end


section

variable {n : ℕ}


-- ==================================  `Ellipsoid.zonoBundle`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as a bundle of one -/
noncomputable def Ellipsoid.zonoBundle (E : Ellipsoid n) : ZonoBundle (Vec ℝ n) :=
  E.zonotope.zonoBundle


-- ==================================  `Interval.zonoBundle`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a bundle of one -/
noncomputable def Interval.zonoBundle (I : Interval (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  I.zonotope.zonoBundle

end


section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ================================  `PolyZonotope.zonoBundle`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as a bundle of one -/
def PolyZonotope.zonoBundle (pZ : PolyZonotope α) : ZonoBundle α :=
  pZ.zonotope.zonoBundle


-- ================================  `SpectraShadow.zonoBundle`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a zonoBundle -/
noncomputable def SpectraShadow.zonoBundle (S : SpectraShadow α) : ZonoBundle α :=
  S.zonotope.zonoBundle

end


section

variable {n : ℕ}


-- ==================================  `VPolytope.zonoBundle`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a bundle of one -/
noncomputable def VPolytope.zonoBundle (P : VPolytope (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  P.zonotope.zonoBundle

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
