module

public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapMono
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusMono
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapMixedExact

@[expose] public section

/-!
# `varInputs` grows with the sets it runs on

`[2]`'s property (7) for `[1, Eq. 7]`'s operator, which `[2, Lemma 3]` assumes of every operation
`[2, Alg. 2]` composes and never proves of any: here it is proved, and it costs nothing. Every
piece of `varInputs` is exact — `mtimes`, `map`, `plus`, `quadMapMixed` twice and `quadMap` once
— so what it denotes is a Minkowski sum of images of its arguments' own sets, and an image and
a sum are both monotone. The third argument is held fixed: `UΔ` is the step's input range, not a
set `[2, Alg. 1]`'s loop grows.

## Inputs
* `B` – input matrix
* `D` – Hessian family
* `Rz₁` – smaller state-input range
* `Rz₂` – larger state-input range
* `RzΔ₁` – smaller varying range
* `RzΔ₂` – larger varying range
* `UΔ` – varying input range

## Hypotheses
* `hz` – state-input ranges nested
* `hzΔ` – varying ranges nested

## Conclusion
* widening either range widens the varying input part

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control, 2013.
* [2] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix

variable {n m o : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `quadMapMixed` is exact, so it grows with either of its two ranges. -/
theorem aux_quadMapMixed_mono (Q : Fin n → Mat ℝ o o) {A₁ A₂ B₁ B₂ : PolyZonotope (Vec ℝ o)}
    (hA : A₁.construct ⊆ A₂.construct) (hB : B₁.construct ⊆ B₂.construct) :
    (PolyZonotope.quadMapMixed Q A₁ B₁).construct
      ⊆ (PolyZonotope.quadMapMixed Q A₂ B₂).construct := by
  rw [← PolyZonotope.quadMapMixed_exact, ← PolyZonotope.quadMapMixed_exact]
  exact Set.image_mono (Set.prod_mono hA hB)

/-- `quadMap` is exact, so it grows with the range it pairs with itself. -/
theorem aux_quadMap_mono (Q : Fin n → Mat ℝ o o) {A₁ A₂ : PolyZonotope (Vec ℝ o)}
    (hA : A₁.construct ⊆ A₂.construct) :
    (A₁.quadMap Q).construct ⊆ (A₂.quadMap Q).construct := by
  rw [← PolyZonotope.quadMap_exact, ← PolyZonotope.quadMap_exact]
  exact Set.image_mono hA


-- =======================================  MAIN THEOREM  ======================================= --

/-- Widening either range widens what `varInputs` admits. -/
theorem varInputs_mono (B : Mat ℝ n m) (D : Fin n → Mat ℝ o o)
    {Rz₁ Rz₂ RzΔ₁ RzΔ₂ : PolyZonotope (Vec ℝ o)} {UΔ : PolyZonotope (Vec ℝ m)}
    (hz : Rz₁.construct ⊆ Rz₂.construct) (hzΔ : RzΔ₁.construct ⊆ RzΔ₂.construct) :
    (varInputs B D Rz₁ RzΔ₁ UΔ).construct ⊆ (varInputs B D Rz₂ RzΔ₂ UΔ).construct :=
  PolyZonotope.plus_mono subset_rfl (PolyZonotope.map_mono _
    (PolyZonotope.plus_mono
      (PolyZonotope.plus_mono (aux_quadMapMixed_mono D hz hzΔ)
        (aux_quadMapMixed_mono D hzΔ hz))
      (aux_quadMap_mono D hzΔ)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
