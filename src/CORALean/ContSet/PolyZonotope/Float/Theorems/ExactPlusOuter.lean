module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus

@[expose] public section

/-!
# `PolyZonotope.exactPlus` encloses the exact one at the nominal sets

The exact layer's `exactPlus` of what the two sets' stored floats denote, plus
both error boxes, lies in the float `exactPlus`. A point of the exact one is the
sum of the two nominal points at one common factor value; the float one reads the
same factors through the same exponent matrix and the same generators, so the
two points differ by the center's rounding alone, which `centerResidual` holds.

The error boxes are added rather than threaded through the factors: a box has no
factors to share, so the sum of two boxes is what any point-wise sum can pick up.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the exact sum plus both error boxes lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_exactPlus_nominal (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) : -- --- CONCL ---
    (Real.PolyZonotope.exactPlus (nominal pZ₁) (nominal pZ₂) hp).construct
      ⊆ nominalSet (pZ₁.exactPlus pZ₂ hp)
        + (PolyZonotope.centerResidual pZ₁.c pZ₂.c).construct := by -- --- PROOF ---
  intro y hy
  obtain ⟨a, β, ha, hβ, hy⟩ := Real.PolyZonotope.mem_construct_iff.mp hy
  -- the float point at the same factors and coefficients, off by the center's rounding
  refine ⟨fun i => toReal ((pZ₁.exactPlus pZ₂ hp).c i)
            + (∑ l, toReal ((pZ₁.exactPlus pZ₂ hp).G l i)
                * Real.PolyZonotope.monomial (pZ₁.exactPlus pZ₂ hp).E a l)
            + ∑ j, toReal ((pZ₁.exactPlus pZ₂ hp).GI j i) * β j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
          fun i => toReal (pZ₁.c i) + toReal (pZ₂.c i)
            - toReal ((pZ₁.exactPlus pZ₂ hp).c i),
          Interval.sub_mem_residual fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩, ?_⟩
  funext i
  -- the stored blocks read back as the exact layer's appended ones, entry by entry
  have hG : ∀ l : Fin (pZ₁.h + pZ₂.h), toReal (Fin.append pZ₁.G pZ₂.G l i)
      = Fin.append (nominal pZ₁).G (nominal pZ₂).G l i :=
    Fin.addCases
      (fun l => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left (nominal pZ₁).G (nominal pZ₂).G l) i).symm)
      fun l => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right (nominal pZ₁).G (nominal pZ₂).G l) i).symm
  have hGI : ∀ j : Fin (pZ₁.q + pZ₂.q), toReal (Fin.append pZ₁.GI pZ₂.GI j i)
      = Fin.append (nominal pZ₁).GI (nominal pZ₂).GI j i :=
    Fin.addCases
      (fun j => by
        rw [Fin.append_left]
        exact (congrFun (Fin.append_left (nominal pZ₁).GI (nominal pZ₂).GI j) i).symm)
      fun j => by
        rw [Fin.append_right]
        exact (congrFun (Fin.append_right (nominal pZ₁).GI (nominal pZ₂).GI j) i).symm
  rw [hy i]
  simp only [Pi.add_apply, Real.PolyZonotope.exactPlus, PolyZonotope.exactPlus, hG, hGI]
  -- the two exponent matrices agree only up to unfolding `nominal`, so match by defeq
  have key : ∀ d A B c₁ c₂ : ℝ, d + A + B + (c₁ + c₂ - d) = c₁ + c₂ + A + B :=
    fun _ _ _ _ _ => by ring
  exact key _ _ _ _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.exactPlus_outer (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) : -- --- CONCL ---
    (Real.PolyZonotope.exactPlus (nominal pZ₁) (nominal pZ₂) hp).construct
        + (pZ₁.I_error.construct + pZ₂.I_error.construct)
      ⊆ (pZ₁.exactPlus pZ₂ hp).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨y', hy', r, hr, hyr⟩ := PolyZonotope.aux_exactPlus_nominal pZ₁ pZ₂ hp hy
  refine ⟨y', hy', e + r, Interval.plus_outer _ _ ⟨e, Interval.plus_outer _ _ he, r, hr, rfl⟩, ?_⟩
  have hyr' : y' + r = y := hyr
  show y' + (e + r) = y + e
  rw [← hyr']
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
