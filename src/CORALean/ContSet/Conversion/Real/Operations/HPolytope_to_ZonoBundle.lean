module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIffRows
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalExact
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# A halfspace description as a bundle of one

## Inputs
* none

## Hypotheses
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Output
* zonotope bundle of the polytope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.zonoBundle (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ZonoBundle (Vec ℝ n) :=
  (HPolytope.zonotope up lo).zonoBundle

/-- CORA's `@polytope/zonoBundle`: one zonotope per row, the box of the vertices in the row's
orthogonal basis, mapped back. -/
noncomputable def HPolytope.zonoBundleRows [NeZero n] (P : HPolytope (Vec ℝ n))
    (V : VPolytope (Vec ℝ n)) [NeZero V.k] (B : Fin (P.m + (P.me + P.me)) → Mat ℝ n n) :
    ZonoBundle (Vec ℝ n) where
  k := P.m + (P.me + P.me)
  Z := fun i =>
    let V_ := fun j => (B i)ᵀ *ᵥ V.V j                      -- V_ = B' * V
    let box := Interval.enclosePoints V_                     -- interval(min(V_,[],2), max(V_,[],2))
    Zonotope.mtimes (B i) box.zonotope                       -- Z{i} = B * zonotope(box)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
