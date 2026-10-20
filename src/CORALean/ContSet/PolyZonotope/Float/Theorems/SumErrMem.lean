module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Sum
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# The sum of points of boxes is a point of the summed box

`sumErr` encloses: a point from each of `m` boxes sums to a point of their `Interval.plus` fold.

## Inputs
* `m` – number of boxes
* `f` – family of interval vectors
* `e` – family of points

## Hypotheses
* `he` – each point lies in its box

## Conclusion
* the sum of the points lies in the summed box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum of points of boxes is a point of the summed box. -/
theorem PolyZonotope.sumErr_mem {m : ℕ} (f : Fin m → Interval (Vec 𝕋 n)) (e : Fin m → Vec ℝ n)
    (he : ∀ i, e i ∈ (f i).construct) :
    ∑ i, e i ∈ (PolyZonotope.sumErr m f).construct := by -- --- PROOF ---
  induction m with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
    rw [Interval.origin_exact]; rfl
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    exact Interval.plus_outer _ _ ⟨e 0, he 0, _, ih (fun i => f i.succ) (fun i => e i.succ)
      (fun i => he i.succ), rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
