module

public import CORALean.ContSet.Polygon.Real.Polygon
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import CORALean.ContSet.Polygon.Real.Counterexamples.SampledHullCora
public import CORALean.ContSet.Polygon.Real.Theorems.SampledHullMissesCircle
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff

@[expose] public section

/-!
# `@polygon/contains_.m` l. 71-78 on regions

For a set operand converted to a polygon `S'`: accepts when
`withinTol(area(P), area(union(P, S')), tol)`, taken as an absolute tolerance, on the regions
the polyshapes denote.

# CORA's `polygon/contains_` accepts an ellipsoid its polygon does not contain

`@polygon/contains_.m` l. 69 replaces an ellipsoid operand by `polygon(S)`, which
`@ellipsoid/polygon.m` builds from `N = 1000` boundary points, so it lies inside the ellipsoid.
For `P = polygon(E)` and `E = ellipsoid(eye(2))`, `contains(P, E)` compares `area(P)` with
`area(union(P, polygon(E)))`, equal, and returns true, though a boundary point of `E` between two
samples is outside `P`. Holds for every finite sample `V` of boundary points. Read from the source,
not run; the modelled and abstracted parts are in `Polygon.sampledHullCora`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped MatrixOrder


-- The model: CORA's code as printed, kept only to be refuted.
/-- The area of `P` equals that of `union(P, S')` within `tol`. -/
noncomputable def Polygon.containsRegionCora (tol : ℝ) (P S' : Set (Vec ℝ 2)) : Prop :=
  |(MeasureTheory.volume P).toReal - (MeasureTheory.volume (P ∪ S')).toReal| ≤ tol


open CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `P = polygon(E)` for the unit disk `E` and any finite boundary sample `V`, CORA's test
accepts `E` while `E ⊄ P`. -/
theorem Polygon.containsEllipsoid_cora_counterexample (V : Set (Vec ℝ 2)) (hV : V.Finite)
    (hc : ∀ p ∈ V, p 0 ^ 2 + p 1 ^ 2 = 1) (tol : ℝ) (htol : 0 ≤ tol) :
    Polygon.containsRegionCora tol (Polygon.sampledHullCora V) (Polygon.sampledHullCora V) ∧
      ¬ (⟨1, 0, .one⟩ : Ellipsoid 2).construct ⊆ Polygon.sampledHullCora V := by -- --- PROOF ---
  refine ⟨by simpa [Polygon.containsRegionCora] using htol, fun hsub => ?_⟩
  obtain ⟨z, hz, hzn⟩ := Polygon.exists_circle_notMem_sampledHull V hV hc
  refine hzn (hsub ?_)
  have hG : (⟨1, 0, .one⟩ : Ellipsoid 2).G = 1 := CFC.sqrt_one
  refine Ellipsoid.mem_construct_iff.2 ⟨z, ?_, by rw [hG, Matrix.one_mulVec, zero_add]⟩
  show Real.sqrt (∑ i, z i ^ 2) ≤ 1
  rw [Fin.sum_univ_two, hz]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
