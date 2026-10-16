module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.DualBound
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.OfBounds
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.VPolytope.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.Global.Float.EuclideanNorm
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# `ContSet/Conversion/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ====================================  `Capsule.interval`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box, each end rounded away from the capsule. -/
def Capsule.interval (C : Capsule 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => subDown (C.c i) (addUp (absolute (C.g i)) C.r)
  sup := fun i => addUp (C.c i) (addUp (absolute (C.g i)) C.r)

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===================================  `Capsule.ellipsoid`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The scaling `σ` is the one `Interval.ellipsoid` asks for: a float at least `√n`. -/
def Capsule.ellipsoid (C : Capsule 𝕋 n) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  C.interval.ellipsoid σ


-- ===================================  `Capsule.hPolytope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a halfspace polytope, over a floating-point scalar -/
def Capsule.hPolytope (C : Capsule 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  C.interval.hPolytope


-- ==================================  `Capsule.polyZonotope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a polynomial zonotope, over a floating-point scalar -/
def Capsule.polyZonotope (C : Capsule 𝕋 n) : PolyZonotope (Vec 𝕋 n) :=
  C.interval.polyZonotope


-- ====================================  `Capsule.zonotope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a zonotope, over a floating-point scalar -/
def Capsule.zonotope (C : Capsule 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  C.interval.zonotope

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `ConPolyZono.interval`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as a box, over a floating-point scalar -/
def ConPolyZono.interval (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  cPZ.polyZonotope.interval

end


section

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `ConZonotope.zonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Dropping the constraints, over a floating-point scalar -/
def ConZonotope.zonotope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  ⟨cZ.h, cZ.c, cZ.G, cZ.I_error⟩

end


section

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =================================  `ConZonotope.hPolytope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as halfspaces, over a floating-point scalar -/
def ConZonotope.hPolytope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  cZ.zonotope.hPolytope Aq

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `ConZonotope.interval`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a box, over a floating-point scalar -/
def ConZonotope.interval (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  cZ.zonotope.interval

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `ConZonotope.polyZonotope`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a polynomial zonotope, over a floating-point scalar -/
def ConZonotope.polyZonotope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  cZ.zonotope.polyZonotope

end


section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `Ellipsoid.interval`  =================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- CORA's `q ± sqrt(diag(Q))`, given one proposed length `s ≥ √Qᵢᵢ` per coordinate. -/
def Ellipsoid.interval (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => addDown (subDown (E.q i) (absolute (s i))) (E.I_error.inf i)
  sup := fun i => addUp (addUp (E.q i) (absolute (s i))) (E.I_error.sup i)

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =================================  `Ellipsoid.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as a polynomial zonotope, over a floating-point scalar -/
def Ellipsoid.polyZonotope (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : PolyZonotope (Vec 𝕋 n) :=
  (E.interval s).polyZonotope


-- ===================================  `Ellipsoid.zonotope`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An ellipsoid as a zonotope, over a floating-point scalar -/
def Ellipsoid.zonotope (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  (E.interval s).zonotope

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- ===================================  `HPolytope.interval`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a box, over a floating-point scalar -/
def HPolytope.interval (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Interval (Vec 𝕋 n) :=
  Interval.ofBounds up lo


-- ===================================  `HPolytope.zonotope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a zonotope, over a floating-point scalar -/
def HPolytope.zonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Zonotope (Vec 𝕋 n) :=
  (HPolytope.interval up lo).zonotope

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `HPolytope.ellipsoid`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as an ellipsoid, over a floating-point scalar -/
def HPolytope.ellipsoid {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  (HPolytope.zonotope up lo).ellipsoid σ

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =================================  `HPolytope.polyZonotope`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a polynomial zonotope, over a floating-point scalar -/
def HPolytope.polyZonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : PolyZonotope (Vec 𝕋 n) :=
  (HPolytope.zonotope up lo).polyZonotope


-- =================================  `HPolytope.conPolyZono`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a constrained polynomial zonotope, over a floating-point scalar -/
def HPolytope.conPolyZono (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  (HPolytope.polyZonotope up lo).conPolyZono

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `Interval.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a constrained polynomial zonotope, over a floating-point scalar -/
def Interval.conPolyZono (I : Interval (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  I.polyZonotope.conPolyZono

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `Capsule.conPolyZono`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a constrained polynomial zonotope, over a floating-point scalar -/
def Capsule.conPolyZono (C : Capsule 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  C.interval.conPolyZono


-- =================================  `Interval.spectraShadow`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a spectrahedral shadow, over a floating-point scalar -/
def Interval.spectraShadow (I : Interval (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  I.zonotope.spectraShadow


-- =================================  `Capsule.spectraShadow`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a spectrahedral shadow, over a floating-point scalar -/
def Capsule.spectraShadow (C : Capsule 𝕋 n) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  C.interval.spectraShadow

end


section

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===================================  `Interval.vPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as its corners, over a floating-point scalar -/
def Interval.vPolytope (I : Interval (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := 2 ^ n
  V := fun l i => if signEquiv n l i then I.sup i else I.inf i
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===================================  `Capsule.vPolytope`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A capsule as a vertex polytope, over a floating-point scalar -/
def Capsule.vPolytope (C : Capsule 𝕋 n) : VPolytope (Vec 𝕋 n) :=
  C.interval.vPolytope


-- ================================  `ConZonotope.vPolytopeBox`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as vertices, over a floating-point scalar -/
def ConZonotope.vPolytopeBox (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope cZ.interval

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =================================  `HPolytope.vPolytopeBox`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Halfspaces to vertices, over a floating-point scalar -/
def HPolytope.vPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope (HPolytope.interval up lo)

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =================================  `PolyZonotope.ellipsoid`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as an ellipsoid, over a floating-point scalar -/
def PolyZonotope.ellipsoid (pZ : PolyZonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  pZ.zonotope.ellipsoid σ


-- =================================  `ConPolyZono.ellipsoid`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as an ellipsoid, over a floating-point scalar -/
def ConPolyZono.ellipsoid (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  cPZ.polyZonotope.ellipsoid σ

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =================================  `PolyZonotope.hPolytope`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as halfspaces, over a floating-point scalar -/
def PolyZonotope.hPolytope (pZ : PolyZonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  pZ.zonotope.hPolytope Aq

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n qI : ℕ}


-- =================================  `ConPolyZono.hPolytope`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as halfspaces, over a floating-point scalar -/
def ConPolyZono.hPolytope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 qI n) : HPolytope
    𝕋 (Vec 𝕋 n) :=
  cPZ.zonotope.hPolytope Aq

end


section

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `PolyZonotope.taylm`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as an array of Taylor models, over a floating-point scalar -/
def PolyZonotope.taylm (pZ : PolyZonotope (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 (pZ.p + pZ.q) :=
  fun i => ⟨(pZ.c i, 0) :: (List.ofFn (fun j => (pZ.G j i, Fin.append (fun k => pZ.E k j) 0))
    ++ List.ofFn (fun l => (pZ.GI l i, Pi.single (Fin.natAdd pZ.p l) 1))),
    pZ.I_error.inf i, pZ.I_error.sup i, N⟩

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =================================  `PolyZonotope.vPolytope`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polynomial zonotope as its corners, over a floating-point scalar -/
def PolyZonotope.vPolytope (pZ : PolyZonotope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  pZ.zonotope.vPolytope


-- =================================  `ConPolyZono.vPolytope`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained polynomial zonotope as its corners, over a floating-point scalar -/
def ConPolyZono.vPolytope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  cPZ.zonotope.vPolytope

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ===============================  `SpectraShadow.polyZonotope`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a polynomial zonotope, over a floating-point scalar -/
def SpectraShadow.polyZonotope (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (PolyZonotope (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.polyZonotope

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ===================================  `Taylm.conPolyZono`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An array of Taylor models as a constrained polynomial zonotope, over a floating-point scalar -/
def Taylm.conPolyZono (T : Fin m → Taylm 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 m) :=
  (Taylm.polyZonotope T).conPolyZono

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  `Taylm.interval`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An array of float Taylor models as a float box -/
def Taylm.interval {m : ℕ} (T : Fin m → Taylm 𝕋 n) : Interval (Vec 𝕋 m) :=
  ⟨fun i => (T i).bounds.1, fun i => (T i).bounds.2⟩

end


section

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- ==================================  `VPolytope.hPolytope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Vertices to halfspaces, over a floating-point scalar -/
def VPolytope.hPolytope (P : VPolytope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => P.boundDot (Aq i) fun _ => rfl

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===================================  `VPolytope.interval`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a box, over a floating-point scalar -/
def VPolytope.interval (P : VPolytope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  Interval.ofBounds P.boundProj P.boundNegProj


-- ===================================  `VPolytope.zonotope`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a zonotope, over a floating-point scalar -/
def VPolytope.zonotope (P : VPolytope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  P.interval.zonotope


-- ==================================  `VPolytope.ellipsoid`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as an ellipsoid, over a floating-point scalar -/
def VPolytope.ellipsoid (P : VPolytope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  P.zonotope.ellipsoid σ


-- =================================  `VPolytope.polyZonotope`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a polynomial zonotope, over a floating-point scalar -/
def VPolytope.polyZonotope (P : VPolytope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  P.zonotope.polyZonotope


-- =================================  `VPolytope.conPolyZono`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A hull as a constrained polynomial zonotope, over a floating-point scalar -/
def VPolytope.conPolyZono (P : VPolytope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  P.polyZonotope.conPolyZono

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ================================  `ZonoBundle.spectraShadow`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope bundle as a spectrahedral shadow, over a floating-point scalar -/
def ZonoBundle.spectraShadow (zB : ZonoBundle (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  match List.ofFn fun i => Zonotope.spectraShadow (zB.Z i) with
  | [] => SpectraShadow.Inf n                    -- no member: the whole space
  | S :: Ss => Ss.foldl SpectraShadow.inter S    -- `and_` of the members, in order


-- ==================================  `ZonoBundle.zonotope`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One component of a bundle, enclosing it, over a floating-point scalar -/
def ZonoBundle.zonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : Zonotope (Vec 𝕋 n) := zB.Z i


-- ==================================  `ZonoBundle.hPolytope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's halfspaces, at one component, over a floating-point scalar -/
def ZonoBundle.hPolytope {q : ℕ} (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) (Aq : Mat 𝕋 q n) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).hPolytope Aq


-- ==================================  `ZonoBundle.interval`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)

/-- A bundle's box, at one component, over a floating-point scalar -/
def ZonoBundle.interval (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : Interval (Vec 𝕋 n) :=
  (zB.zonotope i).interval

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `ZonoBundle.polyZonotope`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonoBundle as a polynomial zonotope, over a floating-point scalar -/
def ZonoBundle.polyZonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : PolyZonotope (Vec 𝕋 n) :=
  (zB.zonotope i).polyZonotope

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `ZonoBundle.vPolytope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bundle's corners, at one component, over a floating-point scalar -/
def ZonoBundle.vPolytope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : VPolytope (Vec 𝕋 n) :=
  (zB.zonotope i).vPolytope

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ====================================  `Zonotope.capsule`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a capsule, over a floating-point scalar -/
def Zonotope.capsule (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) : Capsule 𝕋 n :=
  Z.interval.capsule k

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `Zonotope.conPolyZono`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a constrained polynomial zonotope, over a floating-point scalar -/
def Zonotope.conPolyZono (Z : Zonotope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  Z.polyZonotope.conPolyZono

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ===============================  `SpectraShadow.conPolyZono`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a constrained polynomial zonotope, over a floating-point scalar -/
def SpectraShadow.conPolyZono (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (ConPolyZono 𝕋 (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.conPolyZono

end


section

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =================================  `ZonoBundle.conPolyZono`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonoBundle as a constrained polynomial zonotope, over a floating-point scalar -/
def ZonoBundle.conPolyZono (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).conPolyZono

end


section

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `Zonotope.conZonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a constrained one, over a floating-point scalar -/
def Zonotope.conZonotope (Z : Zonotope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  ⟨Z.h, Z.c, Z.G, HPolytope.fullspace 𝕋 Z.h, Z.I_error⟩

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `Interval.conZonotope`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a constrained zonotope, over a floating-point scalar -/
def Interval.conZonotope (I : Interval (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  I.zonotope.conZonotope

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ===============================  `SpectraShadow.conZonotope`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a constrained zonotope, over a floating-point scalar -/
def SpectraShadow.conZonotope (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (ConZonotope 𝕋 (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.conZonotope

end


section

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  `Zonotope.taylm`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as an array of Taylor models, over a floating-point scalar -/
def Zonotope.taylm (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)),
    Z.I_error.inf i, Z.I_error.sup i, N⟩

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  `Interval.taylm`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as an array of Taylor models, over a floating-point scalar -/
def Interval.taylm (I : Interval (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 n :=
  I.zonotope.taylm N

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `Zonotope.zonoBundle`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A zonotope as a bundle of one, over a floating-point scalar -/
def Zonotope.zonoBundle (Z : Zonotope (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) := ⟨1, fun _ => Z⟩


-- =================================  `ConZonotope.zonoBundle`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope as a bundle of one, over a floating-point scalar -/
def ConZonotope.zonoBundle (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  cZ.zonotope.zonoBundle

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- ==================================  `HPolytope.zonoBundle`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A halfspace description as a bundle of one, over a floating-point scalar -/
def HPolytope.zonoBundle (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ZonoBundle (Vec 𝕋 n) :=
  (HPolytope.zonotope up lo).zonoBundle

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `Interval.zonoBundle`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box as a bundle of one, over a floating-point scalar -/
def Interval.zonoBundle (I : Interval (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) := I.zonotope.zonoBundle

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ================================  `SpectraShadow.zonoBundle`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A spectrahedral shadow as a zonotope bundle, over a floating-point scalar -/
def SpectraShadow.zonoBundle (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (ZonoBundle (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.zonoBundle

end


section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==================================  `VPolytope.zonoBundle`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A vertex description as a bundle of one, over a floating-point scalar -/
def VPolytope.zonoBundle (P : VPolytope (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  P.zonotope.zonoBundle

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
