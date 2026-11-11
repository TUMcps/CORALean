module

public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit

@[expose] public section

/-!
# A stored product keeps the factors

At one factor value `a` and coefficient vector `β`, the exact image of a nominal point is the stored
image's nominal point at the same `a`, `β`, less a point of the residual: the generators of the
result stay at the factors of the original.

## Inputs
* `M` – matrix
* `pZ` – polynomial zonotope
* `a` – factor values
* `β` – coefficients
* `x` – nominal point

## Hypotheses
* `ha` – the factors are in the unit box
* `hβ` – the coefficients are in the unit box
* `hx` – the point is the nominal point at `a` and `β`

## Conclusion
* some point of the residual closes the gap between the exact and the stored image
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At one factor value `a` and coefficient vector `β`, the exact image of a nominal point is the
stored image's nominal point at the same `a`, `β`, less a point of the residual: the generators of
the result stay at the factors of the original. -/
theorem PolyZonotope.mtimes_point (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin pZ.p → ℝ} {β : Fin pZ.q → ℝ} (ha : ∀ k, |a k| ≤ 1) (hβ : ∀ j, |β j| ≤ 1)
    {x : Vec ℝ n} (hx : ∀ i, x i = toReal (pZ.c i)
      + (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      + ∑ j, toReal (pZ.GI j i) * β j) : -- --- CONCL ---
    ∃ r ∈ (PolyZonotope.mtimesResidual M pZ).toSet, ∀ i, (toRealMat M *ᵥ x) i
      = toReal ((PolyZonotope.mtimes M pZ).c i)
        + (∑ l : Fin pZ.h, toReal ((PolyZonotope.mtimes M pZ).G l i)
            * Real.PolyZonotope.monomial pZ.E a l)
        + (∑ j : Fin pZ.q, toReal ((PolyZonotope.mtimes M pZ).GI j i) * β j)
        + r i := by -- --- PROOF ---
  -- the exact product of a column with row `i` of `M`, and what its stored rounding is short
  set ex : Vec 𝕋 n → Fin m → ℝ := fun g i => ∑ k, toReal (M i k) * toReal (g k)
  set gap : Vec 𝕋 n → Fin m → ℝ := fun g i => ex g i - toReal (mulVecDown M g i)
  have hres : (fun i => gap pZ.c i)
      ∈ (Interval.residual (mulVecDown M pZ.c) (mulVecUp M pZ.c)
          (mulVecDown M pZ.c)).toSet :=
    Interval.sub_mem_residual (fun i => ⟨dotDown_le (M i) pZ.c, le_dotUp (M i) pZ.c⟩)
  -- the two generator blocks' shortfalls, each bounded by a coefficient inside `[-1,1]`
  have hdepBox : (fun i => ∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
      ∈ (PolyZonotope.generatorError (matMulDiff M (fun i l => pZ.G l i))).toSet :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.matMul_close M pZ.G) ha
  have hindBox : (fun i => ∑ j, gap (pZ.GI j) i * β j)
      ∈ (PolyZonotope.generatorError (matMulDiff M (fun i j => pZ.GI j i))).toSet :=
    PolyZonotope.mem_generatorError (PolyZonotope.matMul_close M pZ.GI) hβ
  refine ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hres, _, hdepBox, rfl⟩,
    _, hindBox, rfl⟩, fun i => ?_⟩
  -- the stored generators and their errors recombine into the exact ones
  have hdep : (∑ l, toReal (mulVecDown M (pZ.G l) i) * Real.PolyZonotope.monomial pZ.E a l)
      + (∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
      = ∑ l, ex (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hind : (∑ j, toReal (mulVecDown M (pZ.GI j) i) * β j) + (∑ j, gap (pZ.GI j) i * β j)
      = ∑ j, ex (pZ.GI j) i * β j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  show (toRealMat M *ᵥ x) i = toReal ((PolyZonotope.mtimes M pZ).c i)
        + (∑ l : Fin pZ.h, toReal ((PolyZonotope.mtimes M pZ).G l i)
            * Real.PolyZonotope.monomial pZ.E a l)
        + (∑ j : Fin pZ.q, toReal ((PolyZonotope.mtimes M pZ).GI j i) * β j)
      + ((gap pZ.c i + ∑ l, gap (pZ.G l) i * Real.PolyZonotope.monomial pZ.E a l)
        + ∑ j, gap (pZ.GI j) i * β j)
  rw [PolyZonotope.mulVec_split M pZ.c pZ.G pZ.GI (Real.PolyZonotope.monomial pZ.E a) β hx i]
  simp only [PolyZonotope.mtimes]
  linarith [hdep, hind]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
