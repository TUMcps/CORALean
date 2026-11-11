module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The fiber of a sum

A point of the sum of two sets at one value of the factors of both is the sum of a fiber point of
each: the factors of the sum are those of the first followed by those of the second.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values of the sum
* `x` – point of the first
* `y` – point of the second

## Hypotheses
* `hx` – the first point is in the fiber at the first factors
* `hy` – the second point is in the fiber at the second factors

## Conclusion
* the sum of the points is in the fiber of the sum at `a`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum of a fiber point of each is a fiber point of `plus`, at the factors of both. -/
theorem PolyZonotope.plus_fiber (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    {a : Fin (pZ₁.plus pZ₂).p → ℝ} {x y : Vec ℝ n}
    (hx : x ∈ pZ₁.fiber (fun k => a (Fin.castAdd pZ₂.p k)))
    (hy : y ∈ pZ₂.fiber (fun k => a (Fin.natAdd pZ₁.p k))) : -- --- CONCL ---
    x + y ∈ (pZ₁.plus pZ₂).fiber a := by -- --- PROOF ---
  obtain ⟨β₁, hβ₁, e₁, he₁, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  obtain ⟨β₂, hβ₂, e₂, he₂, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hy
  -- the rounding of the center sum is a point of the residual
  set r : Vec ℝ n := fun i => toReal (pZ₁.c i) + toReal (pZ₂.c i) - toReal ((pZ₁.plus pZ₂).c i)
    with hr
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨Fin.append β₁ β₂, ?_, e₁ + e₂ + r, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · simpa using hβ₁ j
    · simpa using hβ₂ j
  · exact Interval.plus_outer _ _ ⟨e₁ + e₂, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
      r, Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩), rfl⟩
  · funext i
    -- the dependent generators are those of both, at each one's factors
    have hG : ∑ l : Fin (pZ₁.plus pZ₂).h, toReal ((pZ₁.plus pZ₂).G l i)
        * Real.PolyZonotope.monomial (pZ₁.plus pZ₂).E a l
        = (∑ l, toReal (pZ₁.G l i) * Real.PolyZonotope.monomial pZ₁.E
            (fun k => a (Fin.castAdd pZ₂.p k)) l)
          + ∑ l, toReal (pZ₂.G l i) * Real.PolyZonotope.monomial pZ₂.E
            (fun k => a (Fin.natAdd pZ₁.p k)) l := by
      rw [show (∑ l : Fin (pZ₁.plus pZ₂).h, _) = ∑ l : Fin (pZ₁.h + pZ₂.h), _ from rfl,
        Fin.sum_univ_add]
      simp only [PolyZonotope.plus, Fin.append_left, Fin.append_right,
        Real.PolyZonotope.monomial_plusE_left, Real.PolyZonotope.monomial_plusE_right]
    -- the independent generators are side by side
    have hGI : ∑ j : Fin (pZ₁.plus pZ₂).q, toReal ((pZ₁.plus pZ₂).GI j i)
        * Fin.append β₁ β₂ j
        = (∑ j, toReal (pZ₁.GI j i) * β₁ j) + ∑ j, toReal (pZ₂.GI j i) * β₂ j := by
      rw [show (∑ j : Fin (pZ₁.plus pZ₂).q, _) = ∑ j : Fin (pZ₁.q + pZ₂.q), _ from rfl,
        Fin.sum_univ_add]
      simp only [PolyZonotope.plus, Fin.append_left, Fin.append_right]
    repeat rw [PolyZonotope.nominal_point_eq]
    simp only [Pi.add_apply]
    rw [hG, hGI]
    simp only [hr]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
