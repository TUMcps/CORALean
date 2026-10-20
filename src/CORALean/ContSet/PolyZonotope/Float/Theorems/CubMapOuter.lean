module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CubMap
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CubMapDepPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `PolyZonotope.cubMap` over-approximates the cubic map, over a floating-point scalar

Every point of the operand, independent generators and box included, is a point of the nominal set
of `absorbRounding` (`absorbRounding_nominal`), which has no independent generators and no box. At
its factors the stored result's nominal point plus the shortfalls in the error box is the cubic
image (`cubMapDep_point`). The result is an enclosure, not the image: the rounding is paid into the
box.

## Inputs
* `T` – family of cubic form tensors
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the cubic image of the set lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMap_outer (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k)) '' pZ.construct
      ⊆ (pZ.cubMap T).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ :=
    PolyZonotope.mem_nominalSet_iff.mp (PolyZonotope.absorbRounding_nominal pZ hx)
  obtain ⟨e, he, heq⟩ := PolyZonotope.cubMapDep_point T pZ.absorbRounding ha
  -- the independent block of the dependent form is empty
  have hx' : x = fun i => toReal (pZ.absorbRounding.c i)
      + ∑ l, toReal (pZ.absorbRounding.G l i)
        * Real.PolyZonotope.monomial pZ.absorbRounding.E a l := by
    funext i
    have h0 : ∑ j, toReal (pZ.absorbRounding.GI j i) * β j = 0 :=
      Finset.sum_eq_zero fun j _ => (Nat.not_lt_zero _ j.isLt).elim
    rw [hz i, h0, add_zero]
  -- the nominal point at the same factors, and the shortfall in the box
  refine ⟨fun i => ∑ l, toReal ((pZ.absorbRounding.cubMapDep T).G l i)
      * Real.PolyZonotope.monomial (pZ.absorbRounding.cubMapDep T).E a l,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.elim0, ha, fun j => j.elim0, fun i => ?_⟩, e, he,
    ?_⟩
  · have h0 : ∑ j, toReal ((PolyZonotope.cubMap T pZ).GI j i) * (Fin.elim0 : Fin 0 → ℝ) j = 0 :=
      Finset.sum_eq_zero fun j _ => (Nat.not_lt_zero _ j.isLt).elim
    change _ = toReal (zero : 𝕋) + _ + _
    rw [toReal_zero, zero_add]
    exact (add_zero _).symm
  · rw [hx', heq]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
